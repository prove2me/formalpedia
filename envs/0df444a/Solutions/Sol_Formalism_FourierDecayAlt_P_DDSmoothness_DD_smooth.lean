-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:17:32.283403+00:00
-- url     : https://prove2.me/submissions/8d9bbf8e-357e-46ab-9def-d5e310e18072

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_smooth_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_smooth_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_smooth_smul
import Theorems.Thm_Formalism_QuantumDeterminants_unitary_conjugation_holds
import Theorems.Thm_low_smooth_of_k_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hw : PI.UpqRep.IsLowUnitH k r ε lam σ w0) :
    ∀ x ∈ DDsp σ w0, x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hrep := hDS.2.2.1.1.2
  have hconj := Formalism.QuantumDeterminants.unitary_conjugation_holds _ ε (PI.UpqRep.Hpk k r) P hdet hPJ
  have hback : ∀ g, P⁻¹ * (P * g * P⁻¹) * P = g := by
    intro g
    rw [show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      hPP, Matrix.one_mul, Matrix.mul_one]
  have hmul : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b →
      σ (a * b) = (σ a).comp (σ b) := by
    intro a b ha hb
    have ha' := (hconj a).mp ha
    have hb' := (hconj b).mp hb
    have h := hrep _ ha' _ hb'
    simp only [hback] at h
    rw [← h]
    congr 1
    rw [show P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPP, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
  have hinUH : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b →
      PI.UpqRep.inUH (PI.UpqRep.Hpk k r) (a * b) := by
    intro a b ha hb
    unfold PI.UpqRep.inUH at *
    rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * PI.UpqRep.Hpk k r * (a * b) =
      bᴴ * (aᴴ * PI.UpqRep.Hpk k r * a) * b by simp only [Matrix.mul_assoc], ha, hb]
  have hw0 : PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g => σ g w0) :=
    low_smooth_of_k_finite hK k r ε lam H σ w0 hl ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ hw
  have htr : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    intro g hg
    have hgH : PI.UpqRep.inUH (PI.UpqRep.Hpk k r) g := hg
    have hcd : ContDiff ℝ ∞ (fun x : Mx k r => x * g) :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)).contDiff
    show PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g' => σ g' (σ g w0))
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFeq⟩ := hw0 (g₀ * g) (hinUH _ _ hg₀ hgH)
    refine ⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g), hU.preimage hcd.continuous, hgU,
      hF.comp hcd.contDiffOn (fun x hx => hx), ?_⟩
    intro x hx hxH
    have hx' := hFeq (x * g) hx (hinUH _ _ hxH hgH)
    simp only at hx'
    show σ x (σ g w0) = F (x * g)
    rw [← hx', hmul x g hxH hgH]
    rfl
  intro x hx
  unfold DDsp at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    exact htr g hg
  | zero => exact smooth_zero σ
  | add y z _ _ hy hz => exact smooth_add hy hz
  | smul a y _ hy => exact smooth_smul a hy
end Formalism.FourierDecayAlt.P.DDSmoothness
