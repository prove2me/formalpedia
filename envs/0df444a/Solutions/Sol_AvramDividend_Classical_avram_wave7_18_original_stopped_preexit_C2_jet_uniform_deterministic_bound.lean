-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_stopped_preexit_C2_jet_uniform_deterministic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:20:17.682208+00:00
-- url     : https://prove2.me/submissions/314bf91f-94fc-4805-906e-35e54e943a04

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower) (hlu : lower ≤ upper)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hdense : DenseRange r)
    (B : ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤
          min (⨅ k : ℕ,
            if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
                upper < x + X.X (r k) ω - rightLimit D (r k) ω
            then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
        ∀ (s : ℝ≥0), s < T →
          |w (x + X.X s ω - rightLimit D s ω)| ≤ M ∧
          |deriv w (x + X.X s ω - rightLimit D s ω)| ≤ M ∧
          |deriv (deriv w) (x + X.X s ω - rightLimit D s ω)| ≤ M := by
  have hc : ENNReal.ofReal upper < C :=
    hcap upper ⟨hlu, le_rfl⟩
  obtain ⟨M, hM, hjet⟩ :=
    avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band
      X x D hD C w hw lower upper hlower hlu hc
  refine ⟨M, hM, ?_⟩
  intro ω T hT s hs
  have hclock :=
    (avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
      X x D hD C w hw r lower upper hlower hcap hdense B).2
      ω T hT
  exact hjet ω s (hclock.2.1 s hs).1
