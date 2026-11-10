-- Prove2me | solution 2 for AvramDividend.Classical.avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:26:04.321312+00:00
-- url     : https://prove2.me/submissions/e3ad749c-5be2-4e6f-9040-6d6b861eb2ab

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_frozen_prefix_general_mark_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
  obtain ⟨W, hWmeas, hW⟩ :=
    avram_bv_jump8_cadlag_mark_weight_lintegral_borel T g hg
  have hPath : Measurable[𝓕 T]
      (fun ω : Ω => fun t : ℝ≥0 => X.X (min t T) ω) :=
    avram_bv_jump8_original_frozen_prefix_path_filtration_measurable X T
  have hComp : Measurable[𝓕 T]
      (fun ω : Ω => W (fun t : ℝ≥0 => X.X (min t T) ω)) :=
    hWmeas.comp hPath
  convert hComp using 1
  funext ω
  rw [hW (fun t : ℝ≥0 => X.X (min t T) ω)
    (avram_wave7_06_original_frozen_prefix_cadlag_all_horizons X ω T).1
    (avram_wave7_06_original_frozen_prefix_cadlag_all_horizons X ω T).2]
  exact avram_mix_gauss14_original_frozen_prefix_general_mark_lintegral X ω T g hg
