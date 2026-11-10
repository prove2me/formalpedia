-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:21:01.370679+00:00
-- url     : https://prove2.me/submissions/d921c0fb-7ed6-4dd9-89f0-c69181b1c65c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite Lévy activity forces finite actual negative jump count at each fixed horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) ≠ ⊤ := by
  classical
  let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let S : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ Iio (0 : ℝ)
  let g : ℝ → ℝ≥0∞ := fun z => if z < 0 then 1 else 0
  have hS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Iio
  have hg : Measurable g :=
    Measurable.ite measurableSet_Iio measurable_const measurable_const
  have hMarked : Measurable[𝓕 T] (fun ω =>
      ∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂J ω) :=
    avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable X T g hg
  have hEq (ω : Ω) : J ω S =
      (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂J ω) := by
    rw [← lintegral_indicator_one hS]
    apply lintegral_congr
    intro p
    simp [S, g, Set.indicator, Set.mem_prod, Set.mem_Ioc, ite_and]
  have hMeas : Measurable (fun ω => J ω S) := by
    have hGlobal : Measurable (fun ω =>
        ∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂J ω) :=
      hMarked.mono (𝓕.le T) le_rfl
    convert hGlobal using 1
    ext ω
    exact hEq ω
  have hRate :
      (∫⁻ ω, J ω S ∂P) =
        (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    simpa only [J, S, tsub_zero] using
      avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
        X 0 T (by exact zero_le) (Iio (0 : ℝ)) measurableSet_Iio
  have hInt : (∫⁻ ω, J ω S ∂P) ≠ ⊤ := by
    rw [hRate]
    exact ENNReal.mul_ne_top (by simp) hFinite
  have hAE := ae_lt_top hMeas hInt
  filter_upwards [hAE] with ω hω
  exact ne_of_lt hω
