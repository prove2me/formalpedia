-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_positive_small_jump_mesh_coefficient_L2_dct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:44:41.786064+00:00
-- url     : https://prove2.me/submissions/62c388f3-5a1f-4d75-becc-975522d404b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_jump_coefficient_positive_reserve_sequence_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical small-jump coefficient square energies converge on strictly positive reserve bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (hε : 0 < ε) (hεδ : ε < δ)
    (U : ℕ → ℝ) (hU : ∀ k, U k ∈ Icc δ K)
    (u : ℝ) (hu : u ∈ Icc δ K)
    (hlim : Tendsto U atTop (𝓝 u)) :
    Tendsto (fun k =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k + z) - w (U k)) -
            (w (u + z) - w u)) ^ 2) ∂X.ν))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let B : Set ℝ := Ioo (-ε) (0 : ℝ)
  let b : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min (1 : ℝ) (z ^ 2))
  let F : ℕ → ℝ → ℝ≥0∞ := fun k z =>
    B.indicator (fun z =>
      ENNReal.ofReal
        (((w (U k + z) - w (U k)) -
          (w (u + z) - w u)) ^ 2)) z
  obtain ⟨Q, hQ0, hQ⟩ :=
    avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
      w C hw_cont hw_neg hw_smooth δ K hδ hδK hK
  have hwMeas : Measurable w :=
    avram_p4_c_generator_zero_negative_payoff_measurable w hw_cont hw_neg
  have hb : Measurable b :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.min (measurable_id.pow_const 2))
  have hMeasF (k : ℕ) : Measurable (F k) := by
    have h1 : Measurable (fun z : ℝ => w (U k + z)) :=
      hwMeas.comp (measurable_const.add measurable_id)
    have h2 : Measurable (fun z : ℝ => w (u + z)) :=
      hwMeas.comp (measurable_const.add measurable_id)
    have hRaw : Measurable (fun z : ℝ =>
        ENNReal.ofReal
          (((w (U k + z) - w (U k)) -
            (w (u + z) - w u)) ^ 2)) :=
      ENNReal.measurable_ofReal.comp
        (((h1.sub measurable_const).sub (h2.sub measurable_const)).pow_const 2)
    exact hRaw.indicator measurableSet_Ioo
  have hEnergyFin :
      (∫⁻ z, ENNReal.ofReal Q * b z ∂X.ν) < ⊤ := by
    rw [lintegral_const_mul (ENNReal.ofReal Q) hb]
    exact ENNReal.mul_lt_top (by simp) X.ν_integrable
  have hBound (k : ℕ) (z : ℝ) :
      F k z ≤ ENNReal.ofReal Q * b z := by
    by_cases hz : z ∈ B
    · have hzneg : z < 0 := hz.2
      have hPoint := ENNReal.ofReal_le_ofReal
        (hQ (U k) (hU k) u hu z hzneg)
      simpa only [F, Set.indicator_of_mem hz, b,
        ENNReal.ofReal_mul hQ0] using hPoint
    · simp only [F, Set.indicator_of_notMem hz]
      exact bot_le
  have hPoint (z : ℝ) :
      Tendsto (fun k => F k z) atTop (𝓝 (0 : ℝ≥0∞)) := by
    by_cases hz : z ∈ B
    · have hzlb : -ε < z := hz.1
      have hzPost : 0 < u + z := by linarith [hu.1]
      have huPos : 0 < u := lt_of_lt_of_le hδ hu.1
      have hCoef :=
        avram_p4_f3_original_negative_jump_coefficient_positive_reserve_sequence_continuity
          w hw_cont u z huPos hzPost U hlim
      have hDiff : Tendsto
          (fun k => (w (U k + z) - w (U k)) - (w (u + z) - w u))
          atTop (𝓝 (0 : ℝ)) := by
        have hConst : Tendsto
            (fun _ : ℕ => w (u + z) - w u)
            atTop (𝓝 (w (u + z) - w u)) := tendsto_const_nhds
        simpa using (hCoef.sub hConst)
      have hSq : Tendsto
          (fun k =>
            (((w (U k + z) - w (U k)) - (w (u + z) - w u)) ^ 2))
          atTop (𝓝 (0 : ℝ)) := by
        simpa using (hDiff.pow 2)
      have hOfReal :=
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hSq
      simpa [F, Set.indicator_of_mem hz, Function.comp_def] using hOfReal
    · have hZero (k : ℕ) : F k z = 0 :=
        Set.indicator_of_notMem hz _
      simp only [hZero]
      exact tendsto_const_nhds
  have hDCT :=
    MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (fun z => ENNReal.ofReal Q * b z)
      hMeasF
      (fun k => Filter.Eventually.of_forall (hBound k))
      (ne_of_lt hEnergyFin)
      (Filter.Eventually.of_forall hPoint)
  have hEq (k : ℕ) :
      (∫⁻ z, F k z ∂X.ν) =
        (∫⁻ z in Ioo (-ε) (0 : ℝ),
          ENNReal.ofReal
            (((w (U k + z) - w (U k)) -
              (w (u + z) - w u)) ^ 2) ∂X.ν) := by
    dsimp [F, B]
    rw [lintegral_indicator measurableSet_Ioo]
  simpa only [hEq, lintegral_zero] using hDCT
