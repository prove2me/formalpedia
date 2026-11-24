-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.pow_le_of_lb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:32:51.848545+00:00
-- url     : https://prove2.me/submissions/7b0acb55-4009-452b-9e1c-0300c98425fb

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
theorem _root_.solution {m δ : ℝ} {e q : ℕ} (hm : 0 ≤ m) (hδ : 0 < δ) (hq : δ ≤ m ^ q) (he : e ≤ q) :
    m ^ e ≤ (1 + δ⁻¹) * m ^ q := by
  have hi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  rcases le_or_gt 1 m with h1 | h1
  · calc m ^ e ≤ m ^ q := pow_le_pow_right₀ h1 he
      _ ≤ (1 + δ⁻¹) * m ^ q := le_mul_of_one_le_left (by positivity) (by linarith)
  · calc m ^ e ≤ 1 := pow_le_one₀ hm h1.le
      _ = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
      _ ≤ δ⁻¹ * m ^ q := mul_le_mul_of_nonneg_left hq hi
      _ ≤ (1 + δ⁻¹) * m ^ q := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
end Formalism.FourierDecayAlt.P.Ux5
