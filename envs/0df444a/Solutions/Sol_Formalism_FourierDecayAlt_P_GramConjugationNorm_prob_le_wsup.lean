-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramConjugationNorm.prob_le_wsup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:46.827287+00:00
-- url     : https://prove2.me/submissions/3fb4183f-190a-4dd1-afa9-b06d2dc3c045

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramConjugationNorm
open Finset Filter Topology Formalism.FourierDecayAlt.TA
open scoped InnerProductSpace ComplexConjugate
variable {W : Type} [Fintype W]
namespace Formalism.FourierDecayAlt.P.GramConjugationNorm
theorem _root_.solution (len : W → ℕ) (B : ℕ) (th : W → ℝ) (hth : IsProb len B th) (g : W → ℝ) :
    ∑ w, th w * g w ≤ wsup len B g := by
  have h1 : ∀ w ∈ (Finset.univ : Finset W), th w * g w ≤ th w * wsup len B g := by
    intro w _
    by_cases h : th w = 0
    · simp [h]
    · exact mul_le_mul_of_nonneg_left
        (le_ciSup (f := fun w : {w // len w ≤ B} => g w.1) (Set.finite_range _).bddAbove
          ⟨w, hth.2.2 w h⟩) (hth.1 w)
  calc ∑ w, th w * g w ≤ ∑ w, th w * wsup len B g := Finset.sum_le_sum h1
    _ = wsup len B g := by rw [← Finset.sum_mul, hth.2.1, one_mul]
end Formalism.FourierDecayAlt.P.GramConjugationNorm
