-- Prove2me | solution 1 for DetDLP.d4_core_cut_and_unroll_tree_math
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T13:23:26.244646+00:00
-- url     : https://prove2.me/submissions/f46b93f5-95c1-4726-b8c8-7a83a5b56147

import Definitions.Def_DetDLP_D4Plan
import Theorems.Thm_DetDLP_guard_cleared_finite_residual_contraction

open DetDLP DetDLP.D4Plan DetDLP.ResidualScalarOracle Finset Polynomial
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace D4GuardedPlan
noncomputable section
def embed (f : ℤ[X]) (l q : ℕ) : ℤ[X]→+*B f l q :=
  (AdjoinRoot.mk _).comp (Polynomial.mapRingHom (Int.castRingHom (U f q)))

theorem low {R : Type} [CommRing R] (l : ℕ) (P : R[X]) (j : Fin l) :
    (P %ₘ (X^l)).coeff j.val=P.coeff j.val := by
  rw [modByMonic_eq_sub_mul_div,coeff_sub]
  have h : (((X:R[X])^l)*(P /ₘ (X^l))).coeff j.val=0 := by
    rw [mul_comm]; exact (coeff_mul_X_pow' ..).trans (if_neg (Nat.not_le_of_lt j.isLt))
  rw [h,sub_zero]
theorem coord (f : ℤ[X]) (hf : f.Monic) (l q : ℕ) (hq : 0 < q) (P : ℤ[X]) (j : Fin l)
    (i : Fin f.natDegree) (hi : i.val=0) :
    word f l q hf (embed f l q P) j i=(P.coeff j.val:ZMod (2^q)).val := by
  let R:=ZMod (2^q)
  letI : Fact (1<2^q):=⟨one_lt_pow₀ (by decide) hq.ne'⟩
  have deg : 0<(f.map (Int.castRingHom R)).natDegree := by
    rw [hf.natDegree_map]; exact Nat.zero_lt_of_lt i.isLt
  let a : R:=P.coeff j.val
  have lt : (C a).degree < (f.map (Int.castRingHom R)).degree := by
    rw [degree_eq_natDegree (hf.map _).ne_zero]
    exact degree_C_le.trans_lt (by exact_mod_cast deg)
  have cast : Int.castRingHom (U f q) (P.coeff j.val)=AdjoinRoot.mk _ (C a) := by
    change (P.coeff j.val:U f q)=AdjoinRoot.of _ (P.coeff j.val:R)
    exact (map_intCast (AdjoinRoot.of (f.map (Int.castRingHom R))) (P.coeff j.val)).symm
  unfold word
  change (((AdjoinRoot.modByMonicHom (hf.map (Int.castRingHom R)) ((AdjoinRoot.modByMonicHom (monic_X_pow l) (AdjoinRoot.mk _ (P.map (Int.castRingHom (U f q))))).coeff j.val)).coeff i.val):R).val=_
  rw [AdjoinRoot.modByMonicHom_mk,low,coeff_map,cast,AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (hf.map _)).mpr lt,hi,coeff_C_zero]
theorem guardWord (p g : ℕ) (z : ℤ) :
    (((2:ZMod (2^(g+p)))^g*z).val)/(2^g)=(z:ZMod (2^p)).val := by
  let q:=2^p
  let L:=2^g
  let a:=(z:ZMod (2^(g+p)))
  have strip {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (x : ZMod (n*m)) :
      ((n:ZMod (n*m))*x).val/n=x.val%m := by
    letI : NeZero (n*m):=⟨(Nat.mul_pos hn hm).ne'⟩
    have e : ((n*x.val:ℕ):ZMod (n*m))=n*x := by simp
    rw [←e,ZMod.val_natCast,Nat.mul_mod_mul_left,Nat.mul_div_cancel_left _ hn]
  have v : (((2:ZMod (2^(g+p)))^g)*a).val/(2^g)=a.val%q := by
    generalize a=x
    unfold q; revert x
    rw [pow_add]; intro x
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using strip (Nat.two_pow_pos g) (Nat.two_pow_pos p) x
  rw [show (z:ZMod (2^(g+p)))=a from rfl,v]
  let φ:=ZMod.castHom (show 2^p ∣ 2^(g+p) by rw [pow_add]; exact dvd_mul_left ..) (ZMod (2^p))
  have h:=congrArg φ (ZMod.natCast_zmod_val a)
  have small : (a.val:ZMod (2^p))=(z:ZMod (2^p)) := by simpa only [a,map_natCast,map_intCast] using h
  simpa only [q,ZMod.val_natCast] using congrArg ZMod.val small

theorem recovered (f : ℤ[X]) (hf : f.Monic) (l p g : ℕ) (hp : 0 < p) (P : ℤ[X]) (j : Fin l) (i : Fin f.natDegree) (hi : i.val=0) :
    word f l (g+p) hf ((2:B f l (g+p))^g*embed f l (g+p) P) j i / 2^g=(P.coeff j.val:ZMod (2^p)).val := by
  let φ:=embed f l (g+p)
  have eq : (2:B f l (g+p))^g*φ P = φ (C ((2:ℤ)^g)*P) := by
    simp only [map_mul,map_pow]; congr 2
    exact (show φ (C 2)=2 by simp [φ,embed,map_ofNat]).symm
  rw [eq,coord f hf l (g+p) (by omega) _ j i hi,coeff_C_mul,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  exact guardWord p g _

theorem binary {k : ℕ} (c : Fin k→ZMod 2) (i : ℕ) (hi : i < k) :
    let f:=(X:ℤ[X])^k+∑ j,monomial j.val ((c j).val:ℤ)
    f.coeff i=0 ∨ f.coeff i=1 := by
  intro f
  have h : f.coeff i=((c ⟨i,hi⟩).val:ℤ) := by
    simp only [f,coeff_add,coeff_X_pow,if_neg (Nat.ne_of_lt hi),zero_add,finsetSum_coeff,coeff_monomial]
    rw [sum_eq_single (⟨i,hi⟩:Fin k)]
    · simp
    · intro j _ ne; exact if_neg (fun e => ne (Fin.ext e))
    · simp
  rw [h]; have := ZMod.val_lt (c ⟨i,hi⟩); omega

theorem build {C c : ℕ} (x : Input C c) (f : ℤ[X]) (hf : f.Monic) (hd : f.natDegree=4*Nat.clog 2 x.S)
    (i : Fin f.natDegree) (hi : i.val=0) (g q : ℕ) (hq : q=g+x.p)
    (N : ℕ) (R : Fin N→BipartiteMultigraph) (w : Fin N→B f x.l q)
    (A : (j : Fin N)→AppendixD4.Tensor (R j) (B f x.l q))
    (edges : ∀ j,(R j).nE=4*x.m*x.k)
    (verts : ∀ j,(R j).nV≤4*x.m+64^(Nat.clog 32 (4*x.m)))
    (deg : ∀ j,(R j).maxDeg*x.m≤1217*(C+1)^3*x.b)
    (eq : (∑ j,w j*BTNContract (R j) (A j))=(2:B f x.l q)^g*embed f x.l q (Z x))
    (bits : ∀ n < f.natDegree,f.coeff n=0 ∨ f.coeff n=1) :
    ∃ P : Plan x, ∀ n < P.f.natDegree,P.f.coeff n=0 ∨ P.f.coeff n=1 := by
  subst q
  let P : Plan x :=
    { f:=f, hf:=hf, deg:=hd, zero:=i, zero_val:=hi, guard:=g, N:=N, R:=R, V:=A, w:=w,
      source:=fun u v=>Encoding.encodeList id [input x,countWord u.val,countWord v.val],
      edges:=edges, vertices:=verts, degree:=deg, correct:=by
        unfold answer; congr 1; apply congrArg List.ofFn; funext j
        rw [eq]; exact (recovered f hf _ _ _ x.hp (Z x) j i hi).symm }
  exact ⟨P,bits⟩
end
end D4GuardedPlan

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem solution (one : AppendixD4.OneStep) (C c : ℕ) (hC : 0 < C) (hc : 0 < c) (E : PrimitiveMachine) (o : Fin E.tapeCount) :
    ∃ L₀ : ℕ, ∃ P : (x : Input C c) → L₀ ≤ Nat.clog 2 x.S → entry x E o → Plan x,
      ∀ x hl he, ∀ i < (P x hl he).f.natDegree, (P x hl he).f.coeff i = 0 ∨ (P x hl he).f.coeff i = 1 := by
  classical
  obtain ⟨lo,k₁,k₂,h₁,h₂,red⟩:=guard_cleared_finite_residual_contraction C
  have make (x : Input C c) (hl : max 1 lo ≤ Nat.clog 2 x.S) :
      ∃ P : Plan x, ∀ n<P.f.natDegree, P.f.coeff n=0 ∨ P.f.coeff n=1 := by
    let L:=Nat.clog 2 x.S
    let g:=64*(x.S+1)*(L+1)*2^L*64^(Nat.clog 32 (4*x.m))
    let q:=x.p+g
    obtain ⟨c₀,mon,degree,irr,run⟩:=red (ell:=x.l) x.spec ((le_max_right ..).trans hl)
      (by have := x.hb; omega) x.hm x.lower x.upper x.hS x.mb x.hp x.pS
    let f:=(X:ℤ[X])^(4*L)+∑ j,monomial j.val ((c₀ j).val:ℤ)
    change f.natDegree=4*L at degree
    have hL : 1≤L := (le_max_left ..).trans hl
    let i : Fin f.natDegree:=⟨0,by omega⟩
    let φ:=D4GuardedPlan.embed f x.l q
    let T (v : Fin x.G.nV) (t : Fin (x.G.deg v)→Bool) := φ (∑ j,monomial j.val (x.A v t j:ℤ))
    obtain ⟨N,w,R,A,cnt,props,correct⟩:=run T
    apply D4GuardedPlan.build x f mon degree i rfl g q (Nat.add_comm ..) N R w A
    · intro j; exact (props j).1
    · intro j; exact (props j).2.1
    · intro j; exact (Nat.mul_le_mul_right x.m (le_max_left ..)).trans (props j).2.2.1
    · rw [correct]
      congr 1
      simp only [T,D4Plan.Z,BTNContract,map_sum,map_prod]
      rfl
    · intro n hn
      exact D4GuardedPlan.binary c₀ n (degree ▸ hn)
  choose P bits using make
  exact ⟨max 1 lo,fun x hl _=>P x hl,fun x hl _=>bits x hl⟩
