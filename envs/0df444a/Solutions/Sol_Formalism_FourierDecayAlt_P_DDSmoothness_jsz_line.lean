-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.jsz_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:12:34.98469+00:00
-- url     : https://prove2.me/submissions/94f1adff-b05c-490e-8e89-1dc153081f91

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
theorem _root_.solution (hU : PI.BesselMapUniq.BesselMapUniq) (hPsi : PsiConst)
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {B0 B : H → Wp}
    (h0 : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B0)
    (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B)
    {x0 : H} (hx0 : x0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (hne : B0 x0 ≠ 0) :
    ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B x = κ • B0 x := by
  have hfun : Formalism.QuantumDeterminants.psi k r z c = PI.BesselMapUniq.psiGen k r z (fun _ => c) :=
    funext fun g => hPsi k r z c g
  rw [hfun] at h0 h
  obtain ⟨a, b, hab, hlin⟩ := hU k r ε lam H σ z (fun _ => c) u Wp π hl hσ hz hT (fun _ => hc) hπ B0 B h0 h
  have hb : b ≠ 0 := by
    rintro rfl
    have ha : a ≠ 0 := hab.resolve_right (fun h => h rfl)
    have h2 := hlin x0 hx0
    rw [zero_smul, add_zero, smul_eq_zero] at h2
    exact h2.elim ha hne
  refine ⟨-(a / b), fun x hx => ?_⟩
  have h1 : b • B x = -(a • B0 x) := eq_neg_of_add_eq_zero_right (hlin x hx)
  calc B x = b⁻¹ • (b • B x) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    _ = -(a / b) • B0 x := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
end Formalism.FourierDecayAlt.P.DDSmoothness
