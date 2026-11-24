-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.bessel_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:12:34.972894+00:00
-- url     : https://prove2.me/submissions/e4663141-d8ff-4b8e-8cbb-6153ff380d90

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {σ : Mx k r → (H →L[ℂ] H)}
    {π : Mx k r → (Wp →L[ℂ] Wp)} :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun _ => (0 : Wp)) := by
  refine ⟨fun _ _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => by simp, 0, [], by simp,
    fun _ _ => by simp⟩
end Formalism.FourierDecayAlt.P.DDSmoothness
