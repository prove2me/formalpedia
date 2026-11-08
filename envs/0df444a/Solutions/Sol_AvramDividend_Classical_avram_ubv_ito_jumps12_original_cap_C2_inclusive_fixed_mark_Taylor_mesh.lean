-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps12_original_cap_C2_inclusive_fixed_mark_Taylor_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:20:16.097336+00:00
-- url     : https://prove2.me/submissions/f2e52a12-84ee-4cf8-a416-e69acac9a1da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_stopped_discounted_fixed_mark_taylor_left_mesh_converges
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps11_original_ennreal_cap_C2_to_real_band
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_zero_extended_value_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (ω : Ω) (t : ℝ≥0)
    (s : ℕ → ℝ≥0) (hsle : ∀ n, s n ≤ t)
    (hst : Tendsto s atTop (𝓝 t))
    (w : ℝ → ℝ) (q z : ℝ)
    (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) (hwzero : w 0 = 0)
    (hy : Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t ∈ Ioo (0 : ℝ) c) :
    let K : ℝ≥0 → ℝ := fun u =>
      Real.exp (-(q * (u : ℝ))) *
        ((fun y : ℝ => w (y + z) - w y - z * deriv w y)
          (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u))
    Tendsto
      (fun n => (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
      atTop
      (𝓝 ((if t ≤ τ ω then (1 : ℝ) else 0) * K t)) := by
  have hcont : Continuous w :=
    avram_route_bv_drift10_zero_extended_value_continuous
      w hw_cont hw_neg hwzero
  have hc2 : ContDiffOn ℝ 2 w (Ioo (0 : ℝ) c) :=
    avram_ubv_ito_jumps11_original_ennreal_cap_C2_to_real_band
      cap c hc hcCap w hw_smooth
  have hderOn : ContinuousOn (deriv w) (Ioo (0 : ℝ) c) :=
    hc2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hder : ContinuousAt (deriv w)
      (Function.leftLim
        (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t) :=
    hderOn.continuousAt (isOpen_Ioo.mem_nhds hy)
  exact
    avram_p4_s3_interval_i_original_stopped_discounted_fixed_mark_taylor_left_mesh_converges
      X x D hD τ hτstop ω t s hsle hst w q z
      hcont.continuousAt hcont.continuousAt hder

