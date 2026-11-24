-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:15:42.849225+00:00
-- url     : https://prove2.me/submissions/5ff2175e-b54c-4c3b-aa79-336c2bd07133

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
    {π : Mx k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B) (κ : ℂ) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun x => κ • B x) := by
  obtain ⟨hadd, hsm, heq, C, Ws, hWs, hbd⟩ := hB
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, ‖κ‖ * C, Ws, hWs, fun v hv => ?_⟩
  · simp only [hadd v hv w hw, smul_add]
  · simp only [hsm c v hv]
    exact smul_comm κ c (B v)
  · simp only [heq h hh m hm v hv, map_smul]
    exact smul_comm κ (ψ m) _
  · rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd v hv) (norm_nonneg κ)
end Formalism.FourierDecayAlt.P.DDSmoothness
