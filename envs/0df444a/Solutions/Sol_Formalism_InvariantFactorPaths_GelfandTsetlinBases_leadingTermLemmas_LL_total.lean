-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.LL_total
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:49.707806+00:00
-- url     : https://prove2.me/submissions/b695db72-a5f4-4995-b3ca-d1f242e482a0

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {σ τ : Type*} [LinearOrder τ] (κ : σ → τ)
variable {κ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution {e e' : σ →₀ ℕ} (h : e ≠ e') : LL κ e e' ∨ LL κ e' e := by
  classical
  set S := (e.support ∪ e'.support).filter fun x => e x ≠ e' x with hS
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply h
    ext x
    by_contra hx
    have : x ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      refine ⟨?_, hx⟩
      by_contra hc
      push Not at hc
      exact hx (by rw [hc.1, hc.2])
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty _)
  obtain ⟨x, hxS, hmin⟩ := Finset.exists_min_image S κ hne
  have hxne : e x ≠ e' x := (Finset.mem_filter.1 hxS).2
  have hbefore : ∀ y, κ y < κ x → e y = e' y := by
    intro y hy
    by_contra hne'
    have : y ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      refine ⟨?_, hne'⟩
      by_contra hc
      push Not at hc
      exact hne' (by rw [hc.1, hc.2])
    exact absurd (hmin y this) (not_le.2 hy)
  rcases lt_or_gt_of_ne hxne with hlt | hgt
  · exact Or.inl ⟨x, hlt, hbefore⟩
  · exact Or.inr ⟨x, hgt, fun y hy => (hbefore y hy).symm⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
