-- Prove2me | solution 1 for CatalyticTreeEval.Main.lemma_B_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T01:47:04.176729+00:00
-- url     : https://prove2.me/submissions/189a0aaf-cf54-4a2c-b200-1a4bf4f2702d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CatalyticTreeEval_Main_polynomial_matching_coordinates
import Theorems.Thm_CatalyticTreeEval_Main_coefficient_evaluation_access

set_option autoImplicit false

open CatalyticTreeEval.Main

/-- The source separates the coefficient/evaluation identity from the streaming access converter. -/
theorem solution (P : List Bool → PolySystem) (domain : Set (List Bool))
    (MP ME : Machine) (A : ℝ) (hA : 0 < A)
    (h : ∀ a ∈ domain, (P a).valid ∧
      (((P a).params a).length : ℝ) ≤ 2 ^ (A * (P a).s) ∧
      PolyFamilyAccess MP ((P a).params a) (P a).f (P a).x (A * (P a).s) ∧
      MonomialAccess ME ((P a).params a) (P a).monomials (A * (P a).s)) :
    ∃ (MV : Machine) (C : ℝ), 0 < C ∧
      ∀ a ∈ domain,
      ∃ U V : Fin (P a).N → Vec (P a).m (P a).monomials.length,
        SMatching ((P a).S₀ ∪ {0}) U V ∧
        VectorAccess MV ((P a).params a) U V
          (C * ((P a).s + log₂ (P a).m)) := by
  obtain ⟨MV, C, hC, haccess⟩ := coefficient_evaluation_access P domain MP ME A hA (by
    intro a ha
    have H := h a ha
    exact ⟨H.1.1, H.1.2.1, H.2.1, H.2.2.1, H.2.2.2⟩)
  refine ⟨MV, C, hC, ?_⟩
  intro a ha
  have H := h a ha
  refine ⟨fun i => coefficientCoordinates ((P a).f i) (P a).monomials,
    fun i => evaluationCoordinates ((P a).x i) (P a).monomials, ?_, haccess a ha⟩
  exact polynomial_matching_coordinates (P a).S₀ (P a).f (P a).x (P a).monomials
    H.1.2.2.1 H.2.2.2.1 H.1.2.2.2
