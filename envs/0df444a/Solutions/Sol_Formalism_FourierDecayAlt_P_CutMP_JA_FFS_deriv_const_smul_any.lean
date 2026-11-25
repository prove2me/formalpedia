-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.FFS.deriv_const_smul_any
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:31.115896+00:00
-- url     : https://prove2.me/submissions/8d2394da-e94a-42f3-ae53-c3aa83e75f99

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
theorem _root_.solution (c : ℂ) (h : ℝ → E') (t : ℝ) :
    deriv (fun s => c • h s) t = c • deriv h t := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hd : DifferentiableAt ℝ h t
  · exact deriv_const_smul c hd
  · have hd' : ¬ DifferentiableAt ℝ (fun s => c • h s) t := by
      intro h'
      apply hd
      have e : h = fun s => c⁻¹ • (c • h s) := by
        funext s
        simp [smul_smul, inv_mul_cancel₀ hc]
      rw [e]
      exact h'.const_smul c⁻¹
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', smul_zero]
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
