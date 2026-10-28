-- Prove2me | solution 2 for AvramDividend.Classical.geometric_renewal_explicit_powers_laplace_ac
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:20:02.620542+00:00
-- url     : https://prove2.me/submissions/1b2f783c-b730-4b29-b0fd-2b8d39a5cd92

import Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
import Theorems.Thm_AvramDividend_Classical_additive_convolution_powers_mass
import Theorems.Thm_AvramDividend_Classical_finite_positive_geometric_measure_sum_of_mass_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_convolution_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_geometric_measure_sum
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_nonnegative_halfline_support_of_measure_convolution
import Theorems.Thm_AvramDividend_Classical_geometric_convolution_renewal_positive_part_ac
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Data.ENNReal.Inv
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (hκac : κ ≪ (volume : Measure ℝ))
    (δ : ℝ≥0∞) (hδ : 0 < δ) (hδfin : δ ≠ ⊤)
    (hgap : κ Set.univ < δ) :
    ∃ (m : ℕ → Measure ℝ) (β : Measure ℝ),
      m 0 = Measure.dirac (0 : ℝ) ∧
      (∀ n : ℕ, m (n + 1) = κ.conv (m n)) ∧
      (∀ n : ℕ, SFinite (m n)) ∧
      β = Measure.sum (fun n : ℕ => (δ⁻¹) ^ (n + 1) • m n) ∧
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          (δ⁻¹ * (1 - δ⁻¹ *
            (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹)) := by
  obtain ⟨m, hm0, hms, hsf⟩ := AvramDividend.Classical.exists_sfinite_convolution_power_sequence κ
  haveI := hsf
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hcr : δ⁻¹ * κ Set.univ < 1 := by
    calc δ⁻¹ * κ Set.univ < δ⁻¹ * δ := by
          rw [mul_comm, mul_comm δ⁻¹]
          exact ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.2 hδfin) (ENNReal.inv_ne_top.2 hδ0) hgap
      _ = 1 := ENNReal.inv_mul_cancel hδ0 hδfin
  have hmass := AvramDividend.Classical.additive_convolution_powers_mass κ m hm0 hms hsf
  obtain ⟨-, hpos, hfin⟩ :=
    AvramDividend.Classical.finite_positive_geometric_measure_sum_of_mass_powers m δ⁻¹ (κ Set.univ)
      (ENNReal.inv_pos.2 hδfin) (ENNReal.inv_ne_top.2 hδ0) hcr hmass
  have hsupp : ∀ n, m n (Iio (0 : ℝ)) = 0 := by
    intro n
    induction n with
    | zero => rw [hm0]; simp
    | succ n ih =>
      rw [hms n]
      exact AvramDividend.Classical.nonnegative_halfline_support_of_measure_convolution κ (m n) hκsupp ih
  set β := Measure.sum (fun n : ℕ => (δ⁻¹) ^ (n + 1) • m n) with hβ
  have hβsupp : β (Iio (0 : ℝ)) = 0 := by
    rw [hβ, Measure.sum_apply _ measurableSet_Iio]
    simp [hsupp]
  refine ⟨m, β, hm0, hms, hsf, rfl, hpos, hfin, hβsupp, ?_, ?_, ?_⟩
  · exact AvramDividend.Classical.geometric_convolution_renewal_positive_part_ac κ hκac m hm0 hms hsf _
  · intro x
    exact ne_top_of_le_ne_top hfin (measure_mono (Set.subset_univ _))
  · intro s hs
    rw [AvramDividend.Classical.positiveLaplace_cumulative_measure β s hs hβsupp,
      AvramDividend.Classical.positiveLaplace_geometric_measure_sum m s _ δ⁻¹
        (AvramDividend.Classical.positiveLaplace_convolution_powers κ m s _ hm0 hms hsf rfl)]
