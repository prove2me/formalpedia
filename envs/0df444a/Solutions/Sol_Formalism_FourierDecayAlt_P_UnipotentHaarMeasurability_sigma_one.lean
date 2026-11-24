-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.sigma_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:32:57.499745+00:00
-- url     : https://prove2.me/submissions/3bcf81f0-7a97-4964-ba32-0cdaacdaadca

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroOfAe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
variable {k r : ℕ}
local notation "MX" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
local notation "UHk" => Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
namespace Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
theorem _root_.solution {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : MX → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ) : σ 1 = 1 := by
  obtain ⟨P, hP, hD⟩ := hds
  have h1 := hD.2.2.1.1.1
  have hPu : IsUnit P.det :=
    Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hP.2)
  simpa [Matrix.nonsing_inv_mul P hPu] using h1
end Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
