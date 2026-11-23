-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA2.mean_le_wsup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:23.694196+00:00
-- url     : https://prove2.me/submissions/3b509b3c-9495-41ce-a137-9d84dd8f14a3

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA2
namespace Formalism.FourierDecayAlt.P.TA2
theorem _root_.solution {W : Type} [Fintype W] (len : W → ℕ) (B : ℕ) (th : W × W → ℝ)
    (hth : IsProb2 len B th) (g : W → ℝ) :
    ∑ x, th x * g x.1 ≤ wsup len B g ∧ ∑ x, th x * g x.2 ≤ wsup len B g := by
  have hle : ∀ w, len w ≤ B → g w ≤ wsup len B g := fun w hw =>
    le_ciSup (f := fun w : {w // len w ≤ B} => g w.1) (Set.finite_range _).bddAbove ⟨w, hw⟩
  have hone : ∑ x, th x * wsup len B g = wsup len B g := by rw [← sum_mul, hth.2.1, one_mul]
  constructor
  · rw [← hone]
    refine sum_le_sum fun x _ => ?_
    by_cases h0 : th x = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (hle _ (hth.2.2 x h0).1) (hth.1 x)
  · rw [← hone]
    refine sum_le_sum fun x _ => ?_
    by_cases h0 : th x = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (hle _ (hth.2.2 x h0).2) (hth.1 x)
end Formalism.FourierDecayAlt.P.TA2
