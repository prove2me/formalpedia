-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_legendre_maximizer_with_gradient_identity_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:07.443143+00:00
-- url     : https://prove2.me/submissions/87d96675-c7eb-464e-a23d-f51e5816ff79

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment
import Theorems.Thm_FunctionalInequalities_Analysis_conjugate_maximizer_eq_gradient_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_finite_maximum_of_upperSemicontinuous_linear_decay_readable
import Theorems.Thm_FunctionalInequalities_Analysis_tiltedObjective_data_readable

noncomputable section
section Attainment
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
/-- Every interior point of the actual finite Legendre domain has an actual
primal maximizer. If the real-valued dual is differentiable there, the same
maximizer is its actual gradient. -/
theorem solution
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤}) :
    ∃ z : E,
      (inner ℝ z y : EReal) - φ z = FunctionalInequalities.Analysis.legendre φ y ∧
      (DifferentiableAt ℝ (fun q : E => (FunctionalInequalities.Analysis.legendre φ q).toReal) y →
        z = gradient (fun q : E => (FunctionalInequalities.Analysis.legendre φ q).toReal) y) := by
    rcases FunctionalInequalities.Analysis.tiltedObjective_data_readable φ hφ hlsc y hy with
      ⟨husc, hnotTop, hfinite, a, b, ha, hdecay⟩
    rcases FunctionalInequalities.Analysis.exists_finite_maximum_of_upperSemicontinuous_linear_decay_readable
        (fun x : E => (inner ℝ x y : EReal) - φ x)
        husc hnotTop hfinite a b ha hdecay with
      ⟨z, hzbot, hztop, hmax⟩
    have hle :
        (inner ℝ z y : EReal) - φ z ≤ FunctionalInequalities.Analysis.legendre φ y := by
      change
        (inner ℝ z y : EReal) - φ z ≤
          ⨆ x : E, (inner ℝ x y : EReal) - φ x
      exact le_iSup (fun x : E => (inner ℝ x y : EReal) - φ x) z
    have hge :
        FunctionalInequalities.Analysis.legendre φ y ≤ (inner ℝ z y : EReal) - φ z := by
      change
        (⨆ x : E, (inner ℝ x y : EReal) - φ x) ≤
          (inner ℝ z y : EReal) - φ z
      exact iSup_le (fun x => hmax x)
    have heq :
        (inner ℝ z y : EReal) - φ z = FunctionalInequalities.Analysis.legendre φ y :=
      le_antisymm hle hge
    refine ⟨z, heq, ?_⟩
    intro hd
    exact
      FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient_readable
        φ hφ hy hd z heq
