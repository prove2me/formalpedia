-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_scale_ratio_gap
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T12:13:12.30916+00:00
-- url     : https://prove2.me/submissions/61e3e40e-fa0a-4c35-b255-bd693f57a16e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option autoImplicit false

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (q : ℝ) (hd : 0 < X.drift) :
    (∀ᶠ θ in atTop, 0 < θ ∧ q < X.ψ θ) ∧
      ∀ᶠ β in atTop, 1 / (2 * X.drift) < β / (X.ψ β - q) := by
  have hq : Tendsto (fun θ : ℝ => q / θ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun θ : ℝ => θ⁻¹) atTop (𝓝 0)).const_mul q)
  have hlimit : Tendsto (fun θ : ℝ => (X.ψ θ - q) / θ) atTop (𝓝 X.drift) := by
    have h := (tendsto_const_nhds (x := X.drift)).sub (bv_exponent_gap_div_tendsto_zero X hBV)
    have h := h.sub hq
    simp only [sub_zero] at h
    refine h.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun θ hθ => ?_)
    change X.drift - (X.drift * θ - X.ψ θ) / θ - q / θ = (X.ψ θ - q) / θ
    field_simp [ne_of_gt hθ]
    ring
  have hpos : ∀ᶠ θ : ℝ in atTop, 0 < (X.ψ θ - q) / θ := hlimit.eventually (lt_mem_nhds hd)
  have hupp : ∀ᶠ θ : ℝ in atTop, (X.ψ θ - q) / θ < 2 * X.drift :=
    hlimit.eventually (gt_mem_nhds (show X.drift < 2 * X.drift by linarith))
  have habove : ∀ᶠ θ in atTop, 0 < θ ∧ q < X.ψ θ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hpos] with θ hθ hposθ
    exact ⟨hθ, sub_pos.mp ((div_pos_iff_of_pos_right hθ).mp hposθ)⟩
  refine ⟨habove, ?_⟩
  filter_upwards [habove, hupp] with β hβ hb
  have hd' : 0 < 2 * X.drift := mul_pos (by norm_num) hd
  apply (div_lt_div_iff₀ hd' (sub_pos.mpr hβ.2)).2
  simpa only [one_mul, mul_comm β] using (div_lt_iff₀ hβ.1).1 hb
