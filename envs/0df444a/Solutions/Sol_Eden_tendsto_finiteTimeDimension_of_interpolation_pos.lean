-- Prove2me | solution 1 for Eden.tendsto_finiteTimeDimension_of_interpolation_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:24.740961+00:00
-- url     : https://prove2.me/submissions/12fdf036-3562-4154-9be8-d483860fb8c1

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_DimensionConvergenceCriteria
import Theorems.Thm_Eden_tendsto_spectrumInterpolation_normalized
import Theorems.Thm_Eden_tendsto_finiteTimeDimension_of_lower_tests
import Theorems.Thm_Eden_finiteTimeDimension_eq_kaplanYorke
import Theorems.Thm_Eden_kaplanYorkeDimension_mem_interval
import Theorems.Thm_Eden_normalizedLogSingularValues_antitone
import Theorems.Thm_Eden_spectrumInterpolation_nonneg_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace)
    (hpos : ∀ d ∈ Ioo 0 (asymptoticDimension c p),
      0 < spectrumInterpolation (lyapunovExponent c p) d) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_lower_tests c p
  intro d hd
  have hd₅ : d ∈ Icc 0 5 := ⟨hd.1.le, hd.2.le.trans
    (kaplanYorkeDimension_mem_interval (lyapunovExponent c p)).2⟩
  have he := (tendsto_spectrumInterpolation_normalized c p d).eventually
    (Ioi_mem_nhds (hpos d hd))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with t htpos ht
  rw [finiteTimeDimension_eq_kaplanYorke c ht p]
  exact (spectrumInterpolation_nonneg_iff
    (normalizedLogSingularValues_antitone c ht p) hd₅).mp (le_of_lt htpos)
end Eden
