-- Prove2me | solution 1 for DetDLP.d4b_outer_caps_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T09:11:16.014788+00:00
-- url     : https://prove2.me/submissions/5b19fa1c-4d91-48be-96f6-965bef2ccc9e

import Definitions.Def_DetDLP_D4BOuterInvariant
import Definitions.Def_DetDLP_D4BEntryLengths
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
set_option autoImplicit false
namespace DetDLP.D4BCaps
open Groundwork D4Plan D4BEntry D4BOuter AppendixD4 ResidualScalarOracle DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
noncomputable section
variable {C c : ℕ} {x : Input C c}
private theorem inputCap {M o w y τ σ} (h : RunsWithin M o w y τ σ) : (w.length:ℝ) ≤ σ := by
  obtain ⟨t,f,_,_,_,_,hs⟩ := h
  apply le_trans _ (hs 0 _ (by omega) (.refl _)); exact_mod_cast (show w.length ≤ visitedSpace (locatedInit M w) by
    apply le_trans _ (Finset.single_le_sum (f:=(fun i => ((locatedInit M w).upper i-(locatedInit M w).lower i+1).toNat)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ M.inputTape)); simp [locatedInit]; omega)
private theorem cnt (a q : ℕ) (h : a<2^q) : (countWord a).length ≤ q+1 := by
  by_cases hn : a=0; simp [hn,countWord]; rw [countWord,if_neg hn,Nat.size_eq_bits_len]; exact (Nat.size_le.mpr h).trans (by omega)
private theorem cwle {a b : ℕ} (h : a ≤ b) : (countWord a).length ≤ (countWord b).length := by
  by_cases ha : a=0
  · subst a; by_cases hb : b=0; simp [hb]; simp [countWord,hb,Nat.size_eq_bits_len]; exact Nat.size_pos.mpr (by omega)
  · have hb : b≠0 := by omega
    simp only [countWord,if_neg ha,if_neg hb,Nat.size_eq_bits_len]; exact Nat.size_le_size h
private theorem cwsuc (n : ℕ) : (countWord (n+1)).length ≤ (countWord n).length+1 := by
  by_cases h : n=0; subst n; decide
  have size := Nat.lt_size_self n
  rw [countWord,if_neg (Nat.succ_ne_zero n),countWord,if_neg h,Nat.size_eq_bits_len,Nat.size_eq_bits_len]
  apply Nat.size_le.mpr; rw [pow_succ]; omega
private theorem listCap {α : Type} (f : α → List Bool) (xs : List α) (b : ℕ) (h : ∀ z ∈ xs, (f z).length ≤ b) :
    (Encoding.encodeList f xs).length ≤ (2*b+2)*xs.length+1 := by
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons x xs ih => have hh := h x (by simp); have ht := ih (fun y hy => h y (by simp [hy])); simp [Encoding.encodeList,flen,Nat.mul_succ]; omega
private theorem mat {n q : ℕ} (v : Fin n → ℕ) (h : ∀ i,v i < 2^q) : (encodeNatListBin (List.ofFn v)).length ≤ (2*(q+1)+2)*n+1 := by
  apply (listCap countWord _ (q+1) ?_).trans_eq (by simp); intro z hz; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz; exact cnt _ _ (h i)
private theorem capEnc (P : Plan x) (s : Res P) : (enc P s).length ≤ (2*(qprec P+1)+2)*(x.l*P.f.natDegree)+1 := mat _ (fun _ => ZMod.val_lt _)
private theorem ansCap : (answer x).length ≤ (2*(x.p+1)+2)*x.l+1 := mat _ (fun _ => ZMod.val_lt _)

def atom (e C n : ℕ) := np e n + (2*C+5)*(n+1)*(e+1)+10
def Hbound (y : ℕ) := 10000*(y+1)^4
private theorem pbPow {f : ℕ → ℕ} (h : PB f) (k : ℕ) : PB fun n => f n ^ k := by induction k with | zero => simpa using (PB.const 1) | succ k ih => simpa [pow_succ] using ih.mul h
private theorem atomPB (e C : ℕ) : PB (atom e C) := (((np_pb e).add ((((PB.const (2*C+5)).mul (PB.id'.add (PB.const 1)))).mul (PB.const (e+1))))).add (PB.const 10)
private theorem capPB : PB Hbound := (PB.const 10000).mul (pbPow (PB.id'.add (PB.const 1)) 4)

structure LengthCaps (P : Plan x) (v : DigitsData P) (H : ℕ) : Prop where
  ini : (pair (input x) []).length ≤ H
  out : (answer x).length ≤ H
  hd : ∀ b : D4BOuter.Bits, b.length ≤ 2*need P+1 → (pair (hdState x b) (tagWord 1 (rankQuery x 0))).length ≤ H ∧ (pair (hdState x b) (header P)).length ≤ H
  br : ∀ u s, (pair (brState P u s) (tagWord 1 (rankQuery x (u.val+1)))).length ≤ H ∧ (pair (brState P u s) (branch P u)).length ≤ H
  dg : ∀ u a s t, (pair (dgState P u a s t) (tagWord 2 (dgQuery P u a))).length ≤ H ∧ (pair (dgState P u a s t) (dgAns P v u a)).length ≤ H
  needCap : need P ≤ H

private theorem parts (P : Plan x) (e : ℕ) {A o} (he : Enumerates A o e P) :
    let y := atom e C (size x)
    (input x).length ≤ y ∧ (header P).length ≤ y ∧ qprec P ≤ y ∧ P.f.natDegree ≤ y ∧ x.l ≤ y ∧
    x.b ≤ y ∧ e*x.b ≤ y ∧ (∀ u a, (digitDesc P u a).length ≤ y) := by
  intro y; obtain ⟨hd,_,_,_,hg,hh,hds,_⟩ := he
  have cap := inputCap hd; rw [←np_cast] at cap hh hg
  have hr : (rankQuery x 0).length ≤ np e (size x) := by exact_mod_cast cap
  have hhd : (header P).length ≤ np e (size x) := by exact_mod_cast hh
  have hgd : P.guard ≤ np e (size x) := by exact_mod_cast hg
  have a : (input x).length ≤ (rankQuery x 0).length := memberLen _ _ (List.mem_cons_self ..)
  have df : (polynomialBits P.f).length ≤ (header P).length := memberLen _ _ (by simp)
  simp [polynomialBits] at df
  have hN := (m14a_separator_edge_budget x.spec).1
  have hb := x.lower.trans (Nat.mul_le_mul_left C hN)
  have hk := Nat.mul_le_mul_left (4*x.m) x.hk
  have hS : x.S ≤ size x := Nat.le_add_right ..
  have hm : x.m ≤ 2*x.S := by omega
  have hl := x.lm.trans (Nat.mul_le_mul_left C hm)
  have hmax : 2*C*x.S ≤ (2*C+5)*(size x+1)*(e+1) := by nlinarith only [Nat.mul_le_mul_left (2*C) hS,Nat.zero_le (C*size x*e),Nat.zero_le (size x*e),Nat.zero_le (size x),Nat.zero_le C,Nat.zero_le e,Nat.zero_le (C*e)]
  have hscale : np e (size x) ≤ y := by dsimp [y,atom]; omega
  have eb : e*x.b ≤ (2*C+5)*(size x+1)*(e+1) := calc
    _ ≤ e*(C*(2*(size x))) := Nat.mul_le_mul_left _ (hb.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hS)))
    _ ≤ _ := by nlinarith only [Nat.zero_le (C*size x),Nat.zero_le (size x*e),Nat.zero_le C,Nat.zero_le (C*e),Nat.zero_le (size x),Nat.zero_le e]
  refine ⟨a.trans (hr.trans hscale),hhd.trans hscale,?_,df.trans (hhd.trans hscale),?_,?_,?_,?_⟩
  · dsimp [y,atom,qprec]; have hp := x.pS.trans hS; nlinarith only [hgd,hp,Nat.zero_le (C*size x),Nat.zero_le (C*size x*e),Nat.zero_le (size x*e),Nat.zero_le C,Nat.zero_le (C*e),Nat.zero_le e,Nat.zero_le (size x)]
  · dsimp [y,atom]; nlinarith only [hl,hmax,Nat.zero_le (np e (size x))]
  · dsimp [y,atom]; nlinarith only [hb,hmax,Nat.zero_le (np e (size x))]
  · dsimp [y,atom]; omega
  · intro u a; apply le_trans _ hscale; exact_mod_cast (hds u a).trans_eq (np_cast ..).symm

private theorem frameLen (a b : D4BOuter.Bits) : (pair a b).length = 2*a.length+1+b.length := by simp [pair,frame_correct,flen]

theorem caps (e : ℕ) : ∃ k : ℕ, ∀ (x : Input C c) (P : Plan x) {A o}, Enumerates A o e P → ∀ v : DigitsData P,
    (∀ u a i, v u a i < 2 ^ precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) → LengthCaps P v (np k (size x)) := by
  obtain ⟨k,hk⟩ := capPB.comp (atomPB e C); refine ⟨k,?_⟩
  intro x P A o he v hv; let y := atom e C (size x); let h := Hbound y
  have hH : h ≤ np k (size x) := hk _
  obtain ⟨hI,hhd,hq,hf,hl,hb,heb,hds⟩ := parts P e he
  change (input x).length ≤ y at hI; change (header P).length ≤ y at hhd; change qprec P ≤ y at hq; change P.f.natDegree ≤ y at hf; change x.l ≤ y at hl; change x.b ≤ y at hb; change e*x.b ≤ y at heb
  have ext (b k n : ℕ) : b ≤ y → k ≤ y → n ≤ y → (2*(b+1)+2)*(k*n)+1 ≤ 5*(y+1)^3 := by
    intro hb hk hn; apply le_trans (b:=(2*(y+1)+2)*(y*y)+1) (by gcongr) _; nlinarith only [Nat.zero_le y,Nat.zero_le (y^2),Nat.zero_le (y^3)]
  let Z := 5*(y+1)^3
  have yz : y+3 ≤ Z := by dsimp [Z]; nlinarith only [Nat.zero_le (y^2),Nat.zero_le (y^3),Nat.zero_le y]
  have hs (s : Res P) : (enc P s).length ≤ Z := (capEnc P s).trans (ext _ _ _ hq hl hf)
  have hfc : (encodeNatListBin (fCoeffs P.f (qprec P))).length ≤ Z := by
    apply (mat _ (fun _ => ZMod.val_lt _)).trans; dsimp [Z]; apply le_trans _ (ext (qprec P) 1 P.f.natDegree hq (by dsimp [y,atom]; omega) hf); simp
  have ctx : (ctxWord P).length ≤ 16*Z+17 := by
    apply (listCap id _ Z ?_).trans_eq (by simp; omega)
    intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [id_eq,List.length_replicate,Nat.size_eq_bits_len,Nat.size_pow] <;> first | exact hs _ | exact hfc | omega | have z : P.guard ≤ qprec P := Nat.le_add_right ..; omega
  have rankN : (countWord P.N).length ≤ y := (memberLen _ _ (List.mem_cons_self ..)).trans hhd
  have hr (u : Fin P.N) : (countWord u.val).length ≤ y := (cwle u.isLt.le).trans rankN
  have hnr (i : ℕ) (hi : (countWord i).length ≤ y+1) : (rankQuery x i).length ≤ 4*y+9 := by
    apply (listCap id _ (y+1) ?_).trans (by simp; omega); intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with rfl|rfl <;> simp only [id_eq] <;> omega
  have hout : (answer x).length ≤ Z := by apply ansCap.trans; apply le_trans _ (ext (qprec P) 1 x.l hq (by dsimp [y,atom]; omega) hl); simp; have ht : x.p ≤ qprec P := Nat.le_add_left ..; gcongr
  have hn : need P ≤ y := max_le hq hl
  have c1 : (countWord 1).length = 1 := rfl
  have c2 : (countWord 2).length = 2 := rfl
  have c3 : (countWord 3).length = 2 := rfl
  have hdCap (b : D4BOuter.Bits) (bl : b.length ≤ 2*need P+1) : (hdState x b).length ≤ 12*y+13 := by
    rw [hdState,listWord_eq]; apply (listCap id _ (2*y+1) ?_).trans (by simp; omega); intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with rfl|rfl|rfl <;> simp only [id_eq] <;> first | omega | decide +revert
  have hbr (u : Fin P.N) : (branch P u).length ≤ y := (memberLen _ _ (by simp : branch P u ∈ [input x,header P,branch P u,vecWord (zvec P u)])).trans (hds u (zvec P u))
  have bcap (u : Fin P.N) (s : Res P) : (brState P u s).length ≤ 8*(16*Z+17)+9 := by
    rw [brState,listWord_eq]; apply (listCap id _ (16*Z+17) ?_).trans (by simp; omega); intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with rfl|rfl|rfl|rfl <;> simp only [id_eq] <;> first | exact ctx | have := hr u; have := hs s; omega | decide +revert
  have dcap (u : Fin P.N) (a : Vect P u) (s t : Res P) : (dgState P u a s t).length ≤ 14*(16*Z+17)+15 := by
    have ha : (vecWord a).length ≤ y := (memberLen _ _ (by simp : vecWord a ∈ [input x,header P,branch P u,vecWord a])).trans (hds u a)
    rw [dgState,listWord_eq]; apply (listCap id _ (16*Z+17) ?_).trans (by simp; omega); intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [id_eq] <;> first | exact ctx | have := hr u; have := hs s; have := hs t; have := hbr u; omega | decide +revert
  have pd := he.2.2.2.2.2.2.2
  have qcap (u : Fin P.N) (a : Vect P u) : (dgQuery P u a).length ≤ 10*y+21 := by
    have gr := (memberLen _ _ (List.mem_cons_self ..) : (P.R u).encode.length ≤ (branch P u).length).trans (hbr u)
    obtain ⟨p',l'⟩ := pd u
    unfold dgQuery encodeBTNInstance; apply (listCap id _ (y+1) ?_).trans (by simp; omega); intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with rfl|rfl|rfl|rfl|rfl <;> simp only [id_eq] <;> first | exact (hds u a).trans (by omega) | omega | apply (cnt _ _ Nat.lt_two_pow_self).trans; omega
  have acap (u : Fin P.N) (a : Vect P u) : (dgAns P v u a).length ≤ Z := by apply (mat _ (hv u a)).trans; apply le_trans _ (ext _ 1 _ ((pd u).1.trans heb) (by dsimp [y,atom]; omega) ((pd u).2.trans heb)); simp
  have Hbig : 600*Z+1000 ≤ h := by dsimp [h,Hbound,Z]; nlinarith only [Nat.zero_le y,Nat.zero_le (y^2),Nat.zero_le (y^3),Nat.zero_le (y^4)]
  have c0 : (countWord 0).length = 1 := rfl
  constructor
  · rw [frameLen]; simp; omega
  · omega
  · intro b bl; have := hdCap b bl; have := hnr 0 (by omega); simp [frameLen,tagWord]; omega
  · intro u s; have := bcap u s; have := hnr (u.val+1) ((cwsuc u.val).trans (Nat.add_le_add_right (hr u) _)); have := hbr u; simp [frameLen,tagWord]; omega
  · intro u a s t; have := dcap u a s t; have := qcap u a; have := acap u a; simp [frameLen,tagWord]; omega
  · omega
end
end DetDLP.D4BCaps

open DetDLP DetDLP.D4BOuter DetDLP.D4Plan DetDLP.D4BEntry DetDLP.ResidualScalarOracle OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
theorem solution (C c e : ℕ) : ∃ k : ℕ, ∀ (x : Input C c) (P : Plan x) {A o}, Enumerates A o e P → ∀ v : DigitsData P,
    (∀ u a i, v u a i < 2 ^ precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) →
    let H := np k (size x)
    (pair (input x) []).length ≤ H ∧ (answer x).length ≤ H ∧
    (∀ b : D4BOuter.Bits, b.length ≤ 2*need P+1 → (pair (hdState x b) (tagWord 1 (rankQuery x 0))).length ≤ H ∧ (pair (hdState x b) (header P)).length ≤ H) ∧
    (∀ u s, (pair (brState P u s) (tagWord 1 (rankQuery x (u.val+1)))).length ≤ H ∧ (pair (brState P u s) (branch P u)).length ≤ H) ∧
    (∀ u a s t, (pair (dgState P u a s t) (tagWord 2 (dgQuery P u a))).length ≤ H ∧ (pair (dgState P u a s t) (dgAns P v u a)).length ≤ H) ∧ need P ≤ H := by
  obtain ⟨k,h⟩ := D4BCaps.caps (C:=C) (c:=c) e
  refine ⟨k,?_⟩; intro x P A o he v hv
  obtain ⟨a,b,c,d,e,f⟩ := h x P he v hv; exact ⟨a,b,c,d,e,f⟩
