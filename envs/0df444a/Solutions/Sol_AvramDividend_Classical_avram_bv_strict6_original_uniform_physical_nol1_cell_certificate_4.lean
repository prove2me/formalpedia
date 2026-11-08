-- Prove2me | solution 4 for AvramDividend.Classical.avram_bv_strict6_original_uniform_physical_nol1_cell_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:02:18.081103+00:00
-- url     : https://prove2.me/submissions/29e56d5f-e901-45ae-aa58-c4fca142ba00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_original_two_scale_cell_contact_no_meas
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_two_scale_centered_positive_error_diagonal
import Theorems.Thm_AvramDividend_Classical_avram_a19_physical_strict_horizon_uniform_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∃ (u : ℕ → ℕ → ℝ≥0) (M B Err : ℕ → Ω → ℝ),
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) ∧
      (∀ n ω,
        let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 =>
          x + X.X t ω - rightLimit D t ω) (u n i)
        B n ω =
          (∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧
                ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) *
                ((u n (i + 1) : ℝ) - (u n i : ℝ))
            else 0) +
          (let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
           let R : ℝ≥0 → ℝ := fun t =>
             ((t : ℝ) * X.drift - X.X t ω) - J t
           ∑ i ∈ Finset.range (n + 1),
             (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧
                 ENNReal.ofReal (Z i) < C then
               Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
             else 0) * (R (u n i) - R (u n (i + 1))))) ∧
      (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) ≤
        w x + (M n ω + B n ω) + max (Err n ω) 0) := by
  obtain ⟨u, hgrid, hmono, huniform⟩ := avram_a19_physical_strict_horizon_uniform_grid T hT
  let B : ℕ → Ω → ℝ := fun n ω =>
    (∑ i ∈ Finset.range (n + 1),
      let Z : ℝ := Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (u n i : ℝ))) * (X.generator w Z - q * w Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) +
    (let J : ℝ≥0 → ℝ := fun t =>
       ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
         Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
     let R : ℝ≥0 → ℝ := fun t =>
       ((t : ℝ) * X.drift - X.X t ω) - J t
     ∑ i ∈ Finset.range (n + 1),
       (let Z : ℝ := Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z ∧ ENNReal.ofReal Z < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w Z else 0) *
         (R (u n i) - R (u n (i + 1))))
  have hB : ∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω =
        (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) *
              ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i) else 0) *
             (R (u n i) - R (u n (i + 1)))) := by
    intro n ω
    rfl
  obtain ⟨M, Ec, Ej, η, hηpos, hηlim, hM, hEc, hEj, hBudget, hApprox⟩ :=
    avram_bv_strict10_original_two_scale_cell_contact_no_meas
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
      u hgrid hmono huniform B hB
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  let Err : ℕ → ℕ → Ω → ℝ := fun n k ω => max (Ec n k ω) 0 + max (Ej n k ω) 0
  have hErrEq (n k : ℕ) (ω : Ω) : max (Err n k ω) 0 =
      max (Ec n k ω) 0 + max (Ej n k ω) 0 :=
    max_eq_left (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have hErr : ∀ n k, Integrable (fun ω => max (Err n k ω) 0) P := by
    intro n k
    have hfun : (fun ω => max (Err n k ω) 0) =
        (fun ω => max (Ec n k ω) 0 + max (Ej n k ω) 0) := by
      funext ω
      exact hErrEq n k ω
    rw [hfun]
    exact (hEc n k).add (hEj n k)
  have hChoose : ∀ n (ε : ℝ), 0 < ε →
      ∃ k, (∫ ω, max (Err n k ω) 0 ∂P) ≤ η n + ε ∧
        (∀ᵐ ω ∂P, F n ω ≤ w x + (M n k ω + B n ω) + max (Err n k ω) 0) := by
    intro n ε hε
    obtain ⟨k, hk⟩ := hApprox n ε hε
    refine ⟨k, ?_, ?_⟩
    · have hfun : (fun ω => max (Err n k ω) 0) =
          (fun ω => max (Ec n k ω) 0 + max (Ej n k ω) 0) := by
        funext ω
        exact hErrEq n k ω
      rw [hfun, integral_add (hEc n k) (hEj n k)]
      exact hk
    · filter_upwards [hBudget n k] with ω hω
      calc
        F n ω ≤ w x + (M n k ω + B n ω) +
            max (Ec n k ω) 0 + max (Ej n k ω) 0 := hω
        _ = w x + (M n k ω + B n ω) + max (Err n k ω) 0 := by
          rw [hErrEq]
          ring
  obtain ⟨M', Err', hM', hErr', hErrLim', hBudget'⟩ :=
    avram_bv_strict6_two_scale_centered_positive_error_diagonal P F B (w x)
      M Err η hηpos hηlim hM hErr hChoose
  exact ⟨u, M', B, Err', hgrid, hmono, huniform, hB, hM', hErr', hErrLim', hBudget'⟩
