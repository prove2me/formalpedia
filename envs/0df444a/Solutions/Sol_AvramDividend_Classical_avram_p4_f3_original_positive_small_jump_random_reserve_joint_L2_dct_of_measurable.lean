-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:06:52.089525+00:00
-- url     : https://prove2.me/submissions/b2c74209-0847-4211-ae79-dbe86c3e071f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_small_jump_mesh_coefficient_L2_dct
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical compact reserve mesh convergence in joint probability–Levy small-jump energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (hε : 0 < ε) (hεδ : ε < δ)
    (U : ℕ → Ω → ℝ) (u : Ω → ℝ)
    (hUb : ∀ k ω, U k ω ∈ Icc δ K)
    (hub : ∀ ω, u ω ∈ Icc δ K)
    (hMeasI : ∀ k, Measurable (fun ω =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k ω + z) - w (U k ω)) -
            (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν)))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => U k ω) atTop (𝓝 (u ω))) :
    Tendsto (fun k =>
      (∫⁻ ω, (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k ω + z) - w (U k ω)) -
            (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν) ∂P))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let I : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U k ω + z) - w (U k ω)) -
          (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν)
  obtain ⟨Q, hQ0, hQ⟩ :=
    avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
      w C hw_cont hw_neg hw_smooth δ K hδ hδK hK
  let b : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min (1 : ℝ) (z ^ 2))
  have hb : Measurable b :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.min (measurable_id.pow_const 2))
  have hEnergyFin :
      (∫⁻ z, ENNReal.ofReal Q * b z ∂X.ν) < ⊤ := by
    rw [lintegral_const_mul (ENNReal.ofReal Q) hb]
    exact ENNReal.mul_lt_top (by simp) X.ν_integrable
  have hBound (k : ℕ) (ω : Ω) :
      I k ω ≤ (∫⁻ z, ENNReal.ofReal Q * b z ∂X.ν) := by
    change (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U k ω + z) - w (U k ω)) -
          (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν)
      ≤ (∫⁻ z, ENNReal.ofReal Q * b z ∂X.ν)
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_mono ?_
    intro z
    by_cases hz : z ∈ Ioo (-ε) (0 : ℝ)
    · rw [Set.indicator_of_mem hz]
      have hPoint := ENNReal.ofReal_le_ofReal
        (hQ (U k ω) (hUb k ω) (u ω) (hub ω) z hz.2)
      simpa only [b, ENNReal.ofReal_mul hQ0] using hPoint
    · rw [Set.indicator_of_notMem hz]
      exact bot_le
  have hDomFinite :
      (∫⁻ ω : Ω, (∫⁻ z, ENNReal.ofReal Q * b z ∂X.ν) ∂P) < ⊤ := by
    simpa [lintegral_const] using hEnergyFin
  have hPointAE :
      ∀ᵐ ω ∂P, Tendsto (fun k => I k ω) atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [hlim] with ω hω
    simpa only [I] using
      (avram_p4_f3_original_positive_small_jump_mesh_coefficient_L2_dct
        X w C hw_cont hw_neg hw_smooth δ K ε
        hδ hδK hK hε hεδ (fun k => U k ω)
        (fun k => hUb k ω) (u ω) (hub ω) hω)
  have hDCT :=
    MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (fun _ : Ω => (∫⁻ z, ENNReal.ofReal Q * b z ∂X.ν))
      (fun k => hMeasI k)
      (fun k => Filter.Eventually.of_forall (hBound k))
      (ne_of_lt hDomFinite) hPointAE
  simpa only [I, lintegral_zero] using hDCT
