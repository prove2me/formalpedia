-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityD.general_duality_relations
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:43:20.153282+00:00
-- url     : https://prove2.me/submissions/ee819f4c-e7ef-42ed-a624-64c27677a9a6

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiGen
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GGen

set_option autoImplicit false

universe u

namespace P2fa

lemma sInf_setOf {ι : Sort*} (f : ι → EReal) : sInf {t : EReal | ∃ x, t = f x} = ⨅ x, f x := by
  have : {t : EReal | ∃ x, t = f x} = Set.range f := by ext t; simp [eq_comm]
  rw [this, sInf_range]

lemma sSup_setOf {ι : Sort*} (f : ι → EReal) : sSup {t : EReal | ∃ x, t = f x} = ⨆ x, f x := by
  have : {t : EReal | ∃ x, t = f x} = Set.range f := by ext t; simp [eq_comm]
  rw [this, sSup_range]

lemma neg_iSup' {ι : Sort*} (f : ι → EReal) : -(⨆ i, f i) = ⨅ i, -(f i) := by
  apply le_antisymm
  · exact le_iInf fun i => EReal.neg_le_neg_iff.mpr (le_iSup f i)
  · rw [EReal.le_neg]
    exact iSup_le fun i => EReal.le_neg.mp (iInf_le (fun j => -(f j)) i)

lemma add_cancel (x : EReal) (c : ℝ) : (x + (c : EReal)) + ((-c : ℝ) : EReal) = x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe a =>
    rw [← EReal.coe_add, ← EReal.coe_add]
    congr 1
    ring

lemma iInf_add_coe {ι : Sort*} (f : ι → EReal) (c : ℝ) :
    (⨅ i, f i) + (c : EReal) = ⨅ i, (f i + (c : EReal)) := by
  apply le_antisymm
  · exact le_iInf fun i => by gcongr; exact iInf_le f i
  · have h : (⨅ i, (f i + (c : EReal))) + ((-c : ℝ) : EReal) ≤ ⨅ i, f i := by
      refine le_iInf fun i => ?_
      calc (⨅ i, (f i + (c : EReal))) + ((-c : ℝ) : EReal)
          ≤ (f i + (c : EReal)) + ((-c : ℝ) : EReal) := by gcongr; exact iInf_le _ i
        _ = f i := add_cancel _ _
    have h2 : (⨅ i, (f i + (c : EReal))) + ((-c : ℝ) : EReal) + (c : EReal) ≤ (⨅ i, f i) + (c : EReal) := by gcongr
    have e : (⨅ i, (f i + (c : EReal))) + ((-c : ℝ) : EReal) + (c : EReal)
        = ⨅ i, (f i + (c : EReal)) := by
      have := add_cancel (⨅ i, (f i + (c : EReal))) (-c)
      simpa using this
    rwa [e] at h2

end P2fa

open Classical in
open DiscreteConvex.ConjugacyDualityD in
theorem solution {V : Type u} [Fintype V] [DecidableEq V] (F : (V → ℤ) → (V → ℤ) → WithTop ℝ) :
    (∀ y : V → ℤ, GGen F y = -(ConvexConjE (PhiGen F) (fun v => -y v))) ∧
    (sSup {t : EReal | ∃ y, t = GGen F y} = ConvexConjE (ConvexConjE (PhiGen F)) 0) ∧
    (PhiGen F 0 = sSup {t : EReal | ∃ y, t = GGen F y} ↔
      PhiGen F 0 = ConvexConjE (ConvexConjE (PhiGen F)) 0) := by
  have h1 : ∀ y : V → ℤ, GGen F y = -(ConvexConjE (PhiGen F) (fun v => -y v)) := by
    intro y
    simp only [GGen, KGen, PhiGen, ConvexConjE, P2fa.sInf_setOf, P2fa.sSup_setOf, P2fa.neg_iSup']
    rw [iInf_comm]
    refine iInf_congr fun u => ?_
    rw [EReal.neg_sub (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
      add_comm, ← EReal.coe_neg, P2fa.iInf_add_coe]
    refine iInf_congr fun x => ?_
    congr 2
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have h2 : sSup {t : EReal | ∃ y, t = GGen F y} = ConvexConjE (ConvexConjE (PhiGen F)) 0 := by
    rw [P2fa.sSup_setOf]
    simp only [h1]
    conv_rhs => rw [ConvexConjE, P2fa.sSup_setOf]
    simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, EReal.coe_zero,
      zero_sub]
    exact (neg_surjective (G := V → ℤ)).iSup_comp (fun y => -(ConvexConjE (PhiGen F) y))
  exact ⟨h1, h2, by rw [h2]⟩
