-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:55:29.331793+00:00
-- url     : https://prove2.me/submissions/1d9d7238-72af-4b18-87e0-13007bc75351

import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_raw_R_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The authentic BV generator/drift-residual sum is AE measurable on every deterministic grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (w : ℝ → ℝ)
    (hw : Measurable w)
    (hGen : Measurable (fun y : ℝ => X.generator w y))
    (C : ℝ≥0∞) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (u : ℕ → ℕ → ℝ≥0) :
    ∀ n, AEStronglyMeasurable (fun ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
          else 0) * (R (u n i) - R (u n (i + 1))))) P := by
  intro n
  let Z (i : ℕ) (ω : Ω) : ℝ := Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  let R (t : ℝ≥0) (ω : Ω) : ℝ :=
    ((t : ℝ) * X.drift - X.X t ω) -
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
  let E (i : ℕ) : Set Ω := {ω |
    (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Z i ω ∧ ENNReal.ofReal (Z i ω) < C}
  have hZ (i : ℕ) : Measurable (Z i) :=
    (avram_integration_sweep9_original_controlled_prestate_ambient_measurable
      X x D hD.1.1).comp (measurable_const.prodMk measurable_id)
  have hruin : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD.1.1
  have hE (i : ℕ) : MeasurableSet (E i) := by
    have h₁ : MeasurableSet {ω : Ω |
        (u n i : ℝ≥0∞) < ruinTime X x D ω} :=
      measurableSet_lt measurable_const hruin
    have h₂ : MeasurableSet {ω : Ω | 0 < Z i ω} :=
      measurableSet_lt measurable_const (hZ i)
    have h₃ : MeasurableSet {ω : Ω | ENNReal.ofReal (Z i ω) < C} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp (hZ i)) measurable_const
    exact h₁.inter (h₂.inter h₃)
  let G (i : ℕ) (ω : Ω) : ℝ :=
    if ω ∈ E i then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator w (Z i ω) - q * w (Z i ω)) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  let H (i : ℕ) (ω : Ω) : ℝ :=
    (if ω ∈ E i then
      Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i ω)
    else 0) * (R (u n i) ω - R (u n (i + 1)) ω)
  have hG (i : ℕ) : AEStronglyMeasurable (G i) P := by
    have hf : Measurable (fun ω : Ω =>
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i ω) - q * w (Z i ω)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))) :=
      (measurable_const.mul
        ((hGen.comp (hZ i)).sub
          (measurable_const.mul (hw.comp (hZ i))))).mul measurable_const
    exact (Measurable.ite (hE i) hf measurable_const).aestronglyMeasurable
  have hH (i : ℕ) : AEStronglyMeasurable (H i) P := by
    have hf : Measurable (fun ω : Ω =>
        Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i ω)) :=
      measurable_const.mul ((measurable_deriv w).comp (hZ i))
    have hfactor : Measurable (fun ω : Ω =>
        if ω ∈ E i then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i ω)
        else 0) := Measurable.ite (hE i) hf measurable_const
    have hleft : AEStronglyMeasurable (R (u n i)) P :=
      avram_a19_nonint_original_raw_R_coordinate_measurable X hX hBV (u n i)
    have hright : AEStronglyMeasurable (R (u n (i + 1))) P :=
      avram_a19_nonint_original_raw_R_coordinate_measurable X hX hBV
        (u n (i + 1))
    exact hfactor.aestronglyMeasurable.mul (hleft.sub hright)
  have hGS : AEStronglyMeasurable
      (fun ω : Ω => ∑ i ∈ Finset.range (n + 1), G i ω) P := by
    have hs : AEStronglyMeasurable
        (∑ i ∈ Finset.range (n + 1), fun ω : Ω => G i ω) P := by
      apply Finset.aestronglyMeasurable_sum
      intro i _
      exact hG i
    have heq :
        (fun ω : Ω => ∑ i ∈ Finset.range (n + 1), G i ω) =
          (∑ i ∈ Finset.range (n + 1), fun ω : Ω => G i ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [heq]
    exact hs
  have hHS : AEStronglyMeasurable
      (fun ω : Ω => ∑ i ∈ Finset.range (n + 1), H i ω) P := by
    have hs : AEStronglyMeasurable
        (∑ i ∈ Finset.range (n + 1), fun ω : Ω => H i ω) P := by
      apply Finset.aestronglyMeasurable_sum
      intro i _
      exact hH i
    have heq :
        (fun ω : Ω => ∑ i ∈ Finset.range (n + 1), H i ω) =
          (∑ i ∈ Finset.range (n + 1), fun ω : Ω => H i ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [heq]
    exact hs
  change AEStronglyMeasurable (fun ω : Ω =>
    (∑ i ∈ Finset.range (n + 1), G i ω) +
    (∑ i ∈ Finset.range (n + 1), H i ω)) P
  exact hGS.add hHS
