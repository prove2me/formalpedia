-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_nonint_original_raw_jump_uniform_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:30:11.551413+00:00
-- url     : https://prove2.me/submissions/49bebdc4-8048-43d5-86c3-9bcea1151c0e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_total_aemeasurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_C1_masked_derivative_factor_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a19_generator_uniform_cell_active_set_measurable
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Assemble the authentic BV residual from measurable masked C1 cells and
actual deterministic-time Lévy jump increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    : ∀ n, AEStronglyMeasurable (fun ω =>
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      ∑ i ∈ Finset.range (n + 1),
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1)))) P := by
  intro n
  have hR (t : ℝ≥0) : AEStronglyMeasurable (fun ω : Ω =>
      ((t : ℝ) * X.drift - X.X t ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0)) P := by
    have hXt : Measurable (fun ω : Ω => X.X t ω) :=
      (X.adapted t).mono (𝓕.le t) le_rfl
    have hJ : AEStronglyMeasurable (fun ω : Ω =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0) P := by
      have hEq : (fun ω : Ω =>
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) =ᵐ[P]
          (fun ω : Ω => ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0) := by
        filter_upwards [avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
          with ω hω
        exact (hω 0 t zero_le).2
      exact (avram_p3_a_bvdrift_actual_jump_total_aemeasurable X hBV t).aestronglyMeasurable.congr hEq
    exact (measurable_const.sub hXt).aestronglyMeasurable.sub hJ
  have hcell (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      AEStronglyMeasurable (fun ω : Ω =>
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
        let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
        let Z : ℕ → ℝ := fun j => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1)))) P := by
    let s : Set ℝ := {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
    have hs : IsOpen s := by
      change IsOpen (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' Iio C)
      exact isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
    let Z : Ω → ℝ := fun ω => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    have hZ : Measurable Z :=
      (avram_integration_sweep9_original_controlled_prestate_ambient_measurable
        X x D hD.1.1).comp (measurable_const.prodMk measurable_id)
    let E : Set Ω := {ω : Ω | (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ω ∧ ENNReal.ofReal (Z ω) < C}
    have hE : MeasurableSet E :=
      avram_a19_generator_uniform_cell_active_set_measurable
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump T hT u hgrid hmono huniform n i
        (Finset.mem_range.mp hi)
    have hEi : ∀ ω ∈ E, Z ω ∈ s := by
      intro ω hω
      exact ⟨hω.2.1, hω.2.2⟩
    have hCofAux :=
      avram_a19_nonint_C1_masked_derivative_factor_measurable
        w s hs hw_smooth Z hZ E hE hEi
        (Real.exp (-(q * (u n i : ℝ))))
    have hCof : Measurable (fun ω : Ω =>
        if ω ∈ E then Real.exp (-(q * (u n i : ℝ))) * deriv w (Z ω)
        else 0) := by
      convert hCofAux using 1
      funext ω
      by_cases he : ω ∈ E <;> simp [he]
    have hProd := hCof.aestronglyMeasurable.mul ((hR (u n i)).sub (hR (u n (i + 1))))
    convert hProd using 1 <;> ext ω <;> rfl
  have hSum : AEStronglyMeasurable
      (∑ i ∈ Finset.range (n + 1), fun ω : Ω =>
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
        let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
        let Z : ℕ → ℝ := fun j => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1)))) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i hi
    exact hcell i hi
  convert hSum using 1
  funext ω
  simp only [Finset.sum_apply]
