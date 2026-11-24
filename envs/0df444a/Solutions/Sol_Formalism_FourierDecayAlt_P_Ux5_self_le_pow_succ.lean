-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.self_le_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:48.165661+00:00
-- url     : https://prove2.me/submissions/17895178-5f04-453a-a75a-cd1c308152f3

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {m δ : ℝ} {q : ℕ} (hm : 0 ≤ m) (hδ : 0 < δ) (hq : δ ≤ m ^ q) :
    m ≤ (1 + δ⁻¹) * m ^ (q + 1) := by
  have hi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  rcases le_or_gt 1 m with h1 | h1
  · calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ (q + 1) := pow_le_pow_right₀ h1 (by omega)
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by linarith)
  · calc m = δ⁻¹ * (δ * m) := by field_simp
      _ ≤ δ⁻¹ * (m ^ q * m) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hm) hi
      _ = δ⁻¹ * m ^ (q + 1) := by rw [pow_succ]
      _ ≤ (1 + δ⁻¹) * m ^ (q + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
end Formalism.FourierDecayAlt.P.Ux5
