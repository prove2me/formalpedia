-- Prove2me | solution 1 for DiscreteConvex.LConvexSetsB.admissible_potentials_properties
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:20:53.177888+00:00
-- url     : https://prove2.me/submissions/1a4a33a7-0aa8-4905-9a1f-97637291d3ba

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_DistanceFunction
import Definitions.Def_DiscreteConvex_LConvexSetsB_AdmissiblePotentials
import Definitions.Def_DiscreteConvex_LConvexSetsB_NoNegativeCycle
import Definitions.Def_DiscreteConvex_LConvexSetsB_ShortestDist
import Definitions.Def_DiscreteConvex_LConvexSetsB_TriangleInequality
import Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegerValuedGamma
import Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegralPolyhedron

namespace DisAPP
open DiscreteConvex.LConvexSetsB

noncomputable def γ0 : Fin 2 → Fin 2 → WithTop ℝ := fun u v => (((u.val : ℝ) - v.val : ℝ) : WithTop ℝ)

lemma dist : DistanceFunction γ0 := by intro v; simp [γ0]

lemma tri : TriangleInequality γ0 := by
  intro a b c
  simp only [γ0, ge_iff_le]
  rw [← WithTop.coe_add, WithTop.coe_le_coe]
  linarith

lemma zero_not_mem : (0 : Fin 2 → ℝ) ∉ AdmissiblePotentials γ0 := by
  intro h
  have := h 0 1 (by decide)
  simp only [γ0, Pi.zero_apply, sub_self, WithTop.coe_le_coe] at this
  norm_num at this

lemma sup_ge (f : (Fin 2 → ℝ) → WithTop ℝ) :
    (0 : WithTop ℝ) ≤ ⨆ p ∈ AdmissiblePotentials γ0, f p := by
  refine le_ciSup_of_le (OrderTop.bddAbove _) (0 : Fin 2 → ℝ) ?_
  have : IsEmpty ((0 : Fin 2 → ℝ) ∈ AdmissiblePotentials γ0) := ⟨zero_not_mem⟩
  rw [iSup_of_empty', WithTop.sSup_eq (by simp) (by simp), Set.preimage_empty, Real.sSup_empty]
  rfl

end DisAPP

open DiscreteConvex.LConvexSetsB in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (γ : V → V → WithTop ℝ), DistanceFunction γ →
    ((AdmissiblePotentials γ).Nonempty ↔ NoNegativeCycle γ) ∧
    ((AdmissiblePotentials γ).Nonempty →
      (∀ u v, ShortestDist γ u v = ⨆ p ∈ AdmissiblePotentials γ, (((p v - p u : ℝ)) : WithTop ℝ)) ∧
      AdmissiblePotentials (ShortestDist γ) = AdmissiblePotentials γ) ∧
    (TriangleInequality γ →
      (AdmissiblePotentials γ).Nonempty ∧
      (∀ u v, γ u v = ⨆ p ∈ AdmissiblePotentials γ, (((p v - p u : ℝ)) : WithTop ℝ))) ∧
    (IsIntegerValuedGamma γ → IsIntegralPolyhedron (AdmissiblePotentials γ))) := by
  intro h
  have h3 := ((h DisAPP.γ0 DisAPP.dist).2.2.1 DisAPP.tri).2 0 1
  have h4 := DisAPP.sup_ge (fun p => (((p 1 - p 0 : ℝ)) : WithTop ℝ))
  rw [← h3] at h4
  simp only [DisAPP.γ0] at h4
  rw [← WithTop.coe_zero, WithTop.coe_le_coe] at h4
  norm_num at h4
