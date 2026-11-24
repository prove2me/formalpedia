-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.pj_dens_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:48.080934+00:00
-- url     : https://prove2.me/submissions/5746d914-dde4-4631-a341-f09d24d51708

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_PjDensUpper
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_pj_dens_meas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
variable {G : Type} [MeasurableSpace G] (μ : Measure G) {Hs : Type} [NormedAddCommGroup Hs]
  [InnerProductSpace ℂ Hs] (σ : G → (Hs →L[ℂ] Hs))
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hm : ∀ x y : Hs, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (V : Submodule ℂ Hs) (hV : Dense (V : Set Hs)) (d : ℝ)
    (h : ∀ x ∈ V, ∀ y ∈ V, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (hd : 0 < d) (x y : Hs) :
    Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧ ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 (hV x)
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.1 (hV y)
  set f : ℕ → G → ℝ≥0∞ := fun n g => ENNReal.ofReal (‖⟪v n, σ g (u n)⟫_ℂ‖ ^ 2) with hf
  have hfm : ∀ n, AEMeasurable (f n) μ := fun n => (pj_dens_meas μ σ hm (u n) (v n)).aemeasurable.ennreal_ofReal
  have hpt : ∀ g, Tendsto (fun n => f n g) atTop (𝓝 (ENNReal.ofReal (‖⟪y, σ g x⟫_ℂ‖ ^ 2))) := fun g =>
    ENNReal.tendsto_ofReal (((hvy.inner (((σ g).continuous.tendsto x).comp hux)).norm).pow 2)
  have hF : ∫⁻ g, liminf (fun n => f n g) atTop ∂μ ≤ liminf (fun n => ∫⁻ g, f n g ∂μ) atTop :=
    lintegral_liminf_le' hfm
  have e1 : (fun g => liminf (fun n => f n g) atTop) = fun g => ENNReal.ofReal (‖⟪y, σ g x⟫_ℂ‖ ^ 2) :=
    funext fun g => (hpt g).liminf_eq
  have e2 : ∀ n, ∫⁻ g, f n g ∂μ = ENNReal.ofReal (‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d) := fun n => by
    rw [← (h _ (hu n) _ (hv n)).2,
      ofReal_integral_eq_lintegral_ofReal (h _ (hu n) _ (hv n)).1 (ae_of_all _ fun g => by positivity)]
  have e3 : Tendsto (fun n => ENNReal.ofReal (‖u n‖ ^ 2 * ‖v n‖ ^ 2 / d)) atTop
      (𝓝 (ENNReal.ofReal (‖x‖ ^ 2 * ‖y‖ ^ 2 / d))) :=
    ENNReal.tendsto_ofReal (((hux.norm.pow 2).mul (hvy.norm.pow 2)).div_const d)
  rw [e1] at hF
  simp only [e2] at hF
  rw [e3.liminf_eq] at hF
  have hnn : 0 ≤ᵐ[μ] fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2 := ae_of_all _ fun g => by positivity
  have hme := pj_dens_meas μ σ hm x y
  refine ⟨⟨hme, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hF ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hme]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hF
end Formalism.MainNotions.LeviCoordinates
