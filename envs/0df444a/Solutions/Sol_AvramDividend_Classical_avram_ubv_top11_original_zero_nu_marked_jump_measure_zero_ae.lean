-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top11_original_zero_nu_marked_jump_measure_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:47:22.055519+00:00
-- url     : https://prove2.me/submissions/c69f180d-5d7a-4676-aaa1-f9794246ad81

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_actual_jumpmark_zero_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! Zero actual original positive-time jump marks eliminate the intrinsic
source marked count measure on one probability-one event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧
        X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))) :
    ∀ᵐ ω ∂P, NX ω = 0 := by
  filter_upwards [avram_ubv_top11_original_zero_nu_actual_jumpmark_zero_ae
    X hNuZero] with ω hzero
  have hset : {t : ℝ≥0 | 0 < t ∧
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0} = ∅ := by
    ext t
    constructor
    · rintro ⟨ht, hne⟩
      exact False.elim (hne (hzero t ht))
    · intro h
      simp at h
  rw [hNX ω, hset]
  simp
