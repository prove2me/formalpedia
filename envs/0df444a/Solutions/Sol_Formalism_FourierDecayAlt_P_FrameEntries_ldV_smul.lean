-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameEntries.ldV_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:08:10.931043+00:00
-- url     : https://prove2.me/submissions/c7161582-35d0-469e-8ef4-9d170929fa86

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FrameEntries
theorem _root_.solution (X : Mx k r) (c : ℂ) (f : Mx k r → E) : Q.LdV X (fun x => c • f x) = fun x => c • Q.LdV X f x := by
  funext x
  unfold Q.LdV
  by_cases hc : c = 0
  · simp [hc]
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * x)) 0
  · exact deriv_const_smul c hd
  · rw [deriv_zero_of_not_differentiableAt hd, smul_zero, deriv_zero_of_not_differentiableAt]
    intro h
    apply hd
    have h2 : DifferentiableAt ℝ (fun t : ℝ => c⁻¹ • c • f (NormedSpace.exp ((t : ℂ) • X) * x)) 0 :=
      h.const_smul c⁻¹
    simpa [smul_smul, inv_mul_cancel₀ hc] using h2
end Formalism.FourierDecayAlt.P.FrameEntries
