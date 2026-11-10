-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:25:42.011846+00:00
-- url     : https://prove2.me/submissions/2f99ed11-2ef8-4fcf-b934-b21e5da4aab1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_frozen_prefix_general_mark_lintegral
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Every nonnegative Borel marked jump observable is adapted on original finite prefixes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let G : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u)))
  change Measurable[𝓕 T] F
  have hFG : F = G := by
    funext ω
    exact avram_mix_gauss14_original_frozen_prefix_general_mark_lintegral
      X ω T g hg
  rw [hFG]
  obtain ⟨W, hW, hExact⟩ :=
    avram_bv_jump8_cadlag_mark_weight_lintegral_borel T g hg
  have hGW : G = (fun ω : Ω => W (fun t : ℝ≥0 => X.X (min t T) ω)) := by
    funext ω
    have hCadlag := avram_wave7_06_original_frozen_prefix_cadlag_all_horizons X ω T
    exact (hExact (fun t : ℝ≥0 => X.X (min t T) ω) hCadlag.1 hCadlag.2).symm
  rw [hGW]
  exact hW.comp (avram_bv_jump8_original_frozen_prefix_path_filtration_measurable X T)
