-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_cr_new_finite_killed_geometric_potential_exact_mass_laplace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:41:22.849019+00:00
-- url     : https://prove2.me/submissions/cd496d99-25b0-40fb-9734-83084dc88136

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
import Theorems.Thm_AvramDividend_Classical_additive_convolution_powers_mass
import Theorems.Thm_AvramDividend_Classical_finite_positive_geometric_measure_sum_of_mass_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_convolution_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_geometric_measure_sum
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (κ : Measure ℝ) [SFinite κ] (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (δ : ℝ≥0∞) (hδ : 0 < δ) (hδfin : δ ≠ ⊤)
    (hgap : κ Set.univ < δ) :
    ∃ β : Measure ℝ,
      β Set.univ = δ⁻¹ * (1 - δ⁻¹ * κ Set.univ)⁻¹ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂β) =
          δ⁻¹ * (1 - δ⁻¹ *
            (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹ := by
  obtain ⟨m, hm0, hms, hsf⟩ := AvramDividend.Classical.exists_sfinite_convolution_power_sequence κ
  have hmass := AvramDividend.Classical.additive_convolution_powers_mass κ m hm0 hms hsf
  have hc0 : 0 < δ⁻¹ := ENNReal.inv_pos.mpr hδfin
  have hctop : δ⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hδ.ne'
  have hcr : δ⁻¹ * κ Set.univ < 1 := by
    calc δ⁻¹ * κ Set.univ < δ⁻¹ * δ := ENNReal.mul_lt_mul_right hc0.ne' hctop hgap
      _ = 1 := ENNReal.inv_mul_cancel hδ.ne' hδfin
  have geo := AvramDividend.Classical.finite_positive_geometric_measure_sum_of_mass_powers m δ⁻¹
    (κ Set.univ) hc0 hctop hcr hmass
  have hsupp : ∀ n, m n (Iio 0) = 0 := by
    intro n
    induction n with
    | zero => rw [hm0, Measure.dirac_apply' _ measurableSet_Iio]; simp
    | succ n ih =>
      haveI := hsf n
      rw [hms n, Measure.conv, Measure.map_apply measurable_add measurableSet_Iio]
      have hsub : (fun x : ℝ × ℝ => x.1 + x.2) ⁻¹' Iio 0 ⊆
          (Iio 0 ×ˢ Set.univ) ∪ (Set.univ ×ˢ Iio 0) := by
        intro x hx
        simp only [Set.mem_preimage, Set.mem_Iio] at hx
        by_cases h : x.1 < 0
        · exact Or.inl ⟨h, trivial⟩
        · exact Or.inr ⟨trivial, by simp only [Set.mem_Iio]; linarith⟩
      refine measure_mono_null hsub (measure_union_null ?_ ?_)
      · rw [Measure.prod_prod, hκsupp, zero_mul]
      · rw [Measure.prod_prod, ih, mul_zero]
  refine ⟨Measure.sum (fun n : ℕ => δ⁻¹ ^ (n + 1) • m n), geo.1, ?_, ?_⟩
  · rw [Measure.sum_apply _ measurableSet_Iio]
    simp [hsupp]
  · intro s hs
    have h1 := AvramDividend.Classical.positiveLaplace_convolution_powers κ m s _ hm0 hms hsf rfl
    exact AvramDividend.Classical.positiveLaplace_geometric_measure_sum m s _ δ⁻¹ h1
