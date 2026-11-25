-- Prove2me | solution 1 for DetDLP.d4_residual_digit_entry_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:37:23.056816+00:00
-- url     : https://prove2.me/submissions/43f6c9ce-28c8-460f-90e5-f30f6ab1d759

import Definitions.Def_DetDLP_D4BEntryCall
import Definitions.Def_DetDLP_D4BEntryResources
import Definitions.Def_DetDLP_D4Slice
import Definitions.Def_DetDLP_ResidualScalarOracle

set_option autoImplicit false
set_option maxHeartbeats 800000
open DetDLP DetDLP.D4Slice DetDLP.ResidualScalarOracle DetDLP_W1_Queries
open Finset Polynomial OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

private theorem generic {n : ℕ} (P len shift base : ℕ) (addr xs : Fin n → ℕ) :
    let w := Encoding.encodeList id [List.replicate len true, encodeNatListBin (List.ofFn addr),
      (2^P : ℕ).bits, shift.bits, base.bits, encodeNatListBin (List.ofFn xs)]
    EncodesTruncPoly P len (raw w) (Ideal.Quotient.mk _ (∑ s, monomial (addr s) ((xs s / shift % base : ℕ) : ZMod (2^P)))) := by
  classical
  intro w
  let digit (i : ℕ) := (∑ s, if addr s = i then xs s / shift % base else 0) % 2^P
  refine ⟨fun i => digit i.val, fun _ => Nat.mod_lt _ (by positivity), ?_, ?_⟩
  · simp only [w,raw,field,first_cons,more_cons,id_eq,List.length_replicate,w5_M6Sort.decode_encode,Groundwork.PolyT.bval_bits]
    apply congrArg encodeNatListBin
    have hz : (List.ofFn addr).zip (List.ofFn xs) = List.ofFn (fun j => (addr j, xs j)) := by
      apply List.ext_getElem <;> simp
    rw [hz]
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp [List.map_ofFn,List.sum_ofFn,digit,Function.comp_def]
  · apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    apply X_pow_dvd_iff.mpr
    intro i hi
    rw [coeff_sub, sub_eq_zero]
    change (∑ s, monomial (addr s) ((xs s / shift % base : ℕ) : ZMod (2^P))).coeff i = (∑ j : Fin len, monomial j.val ((digit j.val : ℕ) : ZMod (2^P))).coeff i
    simp only [finsetSum_coeff,coeff_monomial]
    rw [Finset.sum_eq_single (a := (⟨i,hi⟩ : Fin len)) (f := fun j : Fin len => if j.val = i then (digit j.val : ZMod (2^P)) else 0)]
    · simp [digit,Nat.cast_sum,apply_ite]
    · intro j _ hj
      simp [show j.val ≠ i from fun e => hj (Fin.ext e)]
    · simp

open D4BEntry D4Plan AppendixD4

private theorem encoded {C c : ℕ} {x : Input C c} (P : Plan x) (u : Fin P.N)
    (a : Fin (P.R u).nV → Fin (J P u)) (v : Fin (P.R u).nV) (t : Fin ((P.R u).deg v) → Bool) (j : ℕ)
    (hl : spacing P.f (P.R u)*x.l ≤ (pad j (encodePortQuery (digitDesc P u a) v.val (List.ofFn t))).length)
    (hp : precision P.f x.l (P.R u) (h P u) (4*x.m*x.k) ≤ (pad j (encodePortQuery (digitDesc P u a) v.val (List.ofFn t))).length)
    (ha : h P u*(a v).val ≤ (pad j (encodePortQuery (digitDesc P u a) v.val (List.ofFn t))).length)
    (hh : h P u ≤ (pad j (encodePortQuery (digitDesc P u a) v.val (List.ofFn t))).length) :
    let src := residue P.f x.l (P.guard+x.p) P.hf (P.V u v t)
    let w := encodePortQuery (digitDesc P u a) v.val (List.ofFn t)
    EncodesTruncPoly (precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) (spacing P.f (P.R u)*x.l) (process j w src) (query P.f x.l (P.guard+x.p) P.hf (P.R u) (P.V u) (J P u) (h P u) (4*x.m*x.k) a v t) := by
  intro src w
  unfold process
  rw [sliceArgs_spec P u a v t (pad j w) hl hp ha hh]
  let d := P.f.natDegree; let ell := x.l; let K := spacing P.f (P.R u)
  let coord := (finProdFinEquiv (m:=ell) (n:=d)).symm
  let e := ((finProdFinEquiv (m:=d) (n:=ell)).symm.trans (Equiv.prodComm _ _)).trans (finProdFinEquiv (m:=ell) (n:=d))
  have eq := generic (precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) (K*ell) (2^(h P u*(a v).val)) (2^(h P u)) (fun z => (coord z).2.val+K*(coord z).1.val) (fun z => word P.f ell (P.guard+x.p) P.hf (P.V u v t) (coord z).1 (coord z).2)
  change EncodesTruncPoly _ _ (raw _) _
  dsimp only at eq
  convert eq using 2
  all_goals try rfl
  unfold query
  apply congrArg (Ideal.Quotient.mk _)
  apply Fintype.sum_equiv e
  intro z; simp [e,coord,Equiv.prodComm,K,ell]

theorem solution (C c k e : ℕ) (B A : PrimitiveMachine) (ob : Fin B.tapeCount) (oa : Fin A.tapeCount) :
    ∃ (D : PrimitiveMachine) (od : Fin D.tapeCount) (K : ℕ), ∀ {x : Input C c} (P : Plan x),
      Enumerates A oa e P → Sources B ob k P → Digits D od K P := by
  obtain ⟨p,hp⟩ := fuelSpec (C:=C) (c:=c) e
  obtain ⟨D,od,L,hD⟩ := call p B ob
  obtain ⟨i,hi⟩ := lengths (C:=C) (c:=c) e
  obtain ⟨j,hj⟩ := capPB p
  obtain ⟨K,hK⟩ := resource C L k i j
  refine ⟨D,od,K,?_⟩; intro x P he hB u a
  let σ := polyBound k (size x); let r := (x.b:ℝ)/x.m; let τ := σ*(2:ℝ)^((k:ℝ)*r)
  obtain ⟨T,hT,hTK,ht,hs⟩ := hK (size x) x.b (digitDesc P u a).length (np j (np i (size x))) r (by dsimp [r]; positivity) x.hb (sizeBounds P u a).2.1 le_rfl
  refine ⟨T,hT,hTK,?_⟩; intro v t
  let w := encodePortQuery (digitDesc P u a) v.val (List.ofFn t)
  let src := residue P.f x.l (P.guard+x.p) P.hf (P.V u v t)
  have hsrc : src ≠ [] := by unfold src residue encodeNatListBin; generalize List.ofFn _ = xs; cases xs <;> simp [Encoding.encodeList]
  have hτ : 0 ≤ τ := by dsimp [τ,σ,polyBound]; positivity
  have hσ : 0 ≤ σ := by dsimp [σ,polyBound]; positivity
  have hcall := hD w src τ σ hsrc hτ hσ (by rw [show sourceQuery w = _ from sourceQuery_spec P u a v t]; exact hB u v t)
  obtain ⟨hl,hprec,hav,hh⟩ := hp P he u a v t
  refine ⟨process p w src,encoded P u a v t p hl hprec hav hh,?_⟩
  have hcap := (hj w src).trans (np_mono j (hi P he u a v t))
  have hbound : polyBound L (capLen p w src) ≤ polyBound L (np j (np i (size x))) := by simp only [← np_cast]; exact_mod_cast np_mono L hcap
  obtain ⟨s,f,h1,h2,h3,h4,h5⟩ := hcall
  refine ⟨s,f,h1,h2,h3,h4.trans (le_trans ?_ ht),fun z cfg hz tr => (h5 z cfg hz tr).trans (le_trans ?_ hs)⟩ <;> gcongr
