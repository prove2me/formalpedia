-- Prove2me | solution 1 for Formalism.integrable_tsum_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:46:31.806895+00:00
-- url     : https://prove2.me/submissions/4e46d67c-bd38-4780-8a8b-7465f98e0e16

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : ℕ → α → ℝ} (hφ : ∀ n, Integrable (φ n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ φ n x)
    (hsx : ∀ x, Summable (fun n => φ n x)) (hs : Summable fun n => ∫ x, φ n x ∂μ) :
    Integrable (fun x => ∑' n, φ n x) μ := by
  have hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ φ n x := ae_all_iff.mpr h0
  have hm : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ n x)) μ :=
    fun n => (hφ n).aemeasurable.ennreal_ofReal
  have hmeas : AEMeasurable (fun x => ∑' n, ENNReal.ofReal (φ n x)) μ :=
    AEMeasurable.ennreal_tsum hm
  have hlin : ∫⁻ x, ∑' n, ENNReal.ofReal (φ n x) ∂μ = ENNReal.ofReal (∑' n, ∫ x, φ n x ∂μ) := by
    rw [lintegral_tsum hm,
      ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg_of_ae (h0 n)) hs]
    exact tsum_congr fun n => (ofReal_integral_eq_lintegral_ofReal (hφ n) (h0 n)).symm
  have hint := integrable_toReal_of_lintegral_ne_top hmeas (by rw [hlin]; exact ENNReal.ofReal_ne_top)
  refine hint.congr ?_
  filter_upwards [hall] with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg hx (hsx x), ENNReal.toReal_ofReal (tsum_nonneg hx)]
end Formalism
