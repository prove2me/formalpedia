-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:03:24.691845+00:00
-- url     : https://prove2.me/submissions/28c0ff62-f272-4a4c-afd3-9f3ad8da5c65

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A genuinely original small-band signed source integral is a source jump series. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let E : Set (ℝ≥0 × ℝ) :=
      Ioc (0 : ℝ≥0) T ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    (∫ p in E, p.2 ∂N) =
      ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
        E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0 := by
  classical
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let N : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u)))
  let E : Set (ℝ≥0 × ℝ) :=
    Ioc (0 : ℝ≥0) T ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  have hE : MeasurableSet E := by
    dsimp [E]
    exact measurableSet_Ioc.prod measurableSet_Ioc
  have hfmeas : Measurable (E.indicator (fun p : ℝ≥0 × ℝ => p.2)) :=
    measurable_snd.indicator hE
  have hOn : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) E N := by
    simpa only [E, N, j] using
      (avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable X ω T n)
  have hInt : Integrable (E.indicator (fun p : ℝ≥0 × ℝ => p.2)) N := by
    have hOnFull : IntegrableOn
        (E.indicator (fun p : ℝ≥0 × ℝ => p.2)) Set.univ N := by
      apply (integrableOn_indicator_iff hE).2
      simpa using hOn
    simpa using hOnFull
  have hsum :=
    avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum
      X ω (E.indicator (fun p : ℝ≥0 × ℝ => p.2)) hfmeas hInt
  have hrestr :
      (∫ p, E.indicator (fun q : ℝ≥0 × ℝ => q.2) p ∂N) =
        ∫ p in E, p.2 ∂N := integral_indicator hE
  change (∫ p in E, p.2 ∂N) =
    ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
      E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0
  exact hrestr.symm.trans hsum
