-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.norm_sq_le_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:53:28.033526+00:00
-- url     : https://prove2.me/submissions/edae14fc-593f-4a1a-bd0a-3b3a6b6b3a81

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (a u : H) (η : ℝ) (hη : 0 < η) :
    ‖a‖ ^ 2 ≤ (1 + η) * ‖u‖ ^ 2 + (1 + η⁻¹) * ‖u - a‖ ^ 2 := by
  have h1 : ‖a‖ ≤ ‖u‖ + ‖u - a‖ := by
    calc ‖a‖ = ‖u - (u - a)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u‖ + ‖u - a‖ := norm_sub_le _ _
  have h2 : ‖a‖ ^ 2 ≤ (‖u‖ + ‖u - a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e : η * ‖u‖ ^ 2 + η⁻¹ * ‖u - a‖ ^ 2 - 2 * ‖u‖ * ‖u - a‖ = η⁻¹ * (η * ‖u‖ - ‖u - a‖) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ η⁻¹ * (η * ‖u‖ - ‖u - a‖) ^ 2 := by positivity
  nlinarith
end Formalism.FourierDecayAlt.P.PBK
