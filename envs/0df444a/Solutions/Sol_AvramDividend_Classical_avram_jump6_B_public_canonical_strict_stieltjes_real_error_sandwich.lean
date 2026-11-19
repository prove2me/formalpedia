-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_public_canonical_strict_stieltjes_real_error_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:22:21.298413+00:00
-- url     : https://prove2.me/submissions/6c0b0ee4-58d7-40f9-a99b-d503e87e6378

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_original_cell_real_discount_error
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_strict_stopping_clock_has_finite_preruin_buffer
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_strict_stopped_cell_cash_support
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_discount_mesh_error_tends_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ≥0) (n : ℕ) (ht : t ≤ (n : ℝ≥0))
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω) :
    let N : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) * ((1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) t
    let err : ℕ → ℝ := (fun j : ℕ =>
      ∑ i ∈ Finset.range (N j),
        ((∫⁻ r in paymentTimes (ruinTime X x D ω) ∩
            Ioc (v j i : ℝ) (v j (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r)))
            ∂(dividendMeasure D ω)).toReal -
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
            (rightLimit D (v j (i + 1)) ω - rightLimit D (v j i) ω)))
    ∀ j : ℕ, 0 ≤ err j ∧ err j ≤ (q / ((j : ℝ) + 1)) * (rightLimit D t ω - rightLimit D 0 ω) := by
  dsimp only
  intro j
  let m : ℕ := (n + 1) * (j + 1)
  let v : ℕ → ℝ≥0 := fun i =>
    min ((i : ℝ≥0) * ((1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) t
  let μ : Measure ℝ := dividendMeasure D ω
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hmonoD :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hStrategy ω
  have hstep (i : ℕ) : v i ≤ v (i + 1) ∧
      ((v (i + 1) : ℝ) - (v i : ℝ)) ≤
        (1 : ℝ) / ((j : ℝ) + 1) := by
    simpa [v, div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using
      (avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
        1 j t i)
  obtain ⟨ρ, hρ, hρruin⟩ :=
    avram_jump6_B_strict_stopping_clock_has_finite_preruin_buffer
      t (ruinTime X x D ω) hStrict
  have hcell (i : ℕ) :=
    avram_jump6_B_public_original_cell_real_discount_error
      D hStrategy ω q hq (v i) (v (i + 1)) (hstep i).1
      ((1 : ℝ) / ((j : ℝ) + 1)) (by positivity) (hstep i).2
      (paymentTimes (ruinTime X x D ω)) (by
        simpa [v, Nat.cast_add, Nat.cast_one] using
          (avram_jump6_B_original_strict_stopped_cell_cash_support
            X x D ω q t ρ hρ hρruin j i).symm)
  have hL :
      0 ≤ ∑ i ∈ Finset.range m,
        ((∫⁻ r in paymentTimes (ruinTime X x D ω) ∩
            Ioc (v i : ℝ) (v (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂μ).toReal -
          Real.exp (-(q * (v (i + 1) : ℝ))) *
            (rightLimit D (v (i + 1)) ω - rightLimit D (v i) ω)) := by
    apply Finset.sum_nonneg
    intro i hi
    exact (hcell i).1
  have hU :
      (∑ i ∈ Finset.range m,
        ((∫⁻ r in paymentTimes (ruinTime X x D ω) ∩
            Ioc (v i : ℝ) (v (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂μ).toReal -
          Real.exp (-(q * (v (i + 1) : ℝ))) *
            (rightLimit D (v (i + 1)) ω - rightLimit D (v i) ω))) ≤
      (q / ((j : ℝ) + 1)) *
        (rightLimit D t ω - rightLimit D 0 ω) := by
    calc
      _ ≤ ∑ i ∈ Finset.range m,
          (q / ((j : ℝ) + 1)) *
            (rightLimit D (v (i + 1)) ω - rightLimit D (v i) ω) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [μ, div_eq_mul_inv, mul_assoc] using (hcell i).2
      _ = (q / ((j : ℝ) + 1)) *
          (rightLimit D (v m) ω - rightLimit D (v 0) ω) := by
        rw [← Finset.mul_sum]
        exact congrArg (fun a : ℝ => (q / ((j : ℝ) + 1)) * a)
          (Finset.sum_range_sub (fun k : ℕ => rightLimit D (v k) ω) m)
      _ = (q / ((j : ℝ) + 1)) *
          (rightLimit D t ω - rightLimit D 0 ω) := by
        have hcover :=
          avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh n j t ht
        have heq : v m = t := by
          apply min_eq_right
          simpa [v, m, div_eq_mul_inv, mul_assoc] using hcover
        rw [heq]
        simp [v]
  exact ⟨by simpa [μ, m, v] using hL,
    by simpa [μ, m, v] using hU⟩
