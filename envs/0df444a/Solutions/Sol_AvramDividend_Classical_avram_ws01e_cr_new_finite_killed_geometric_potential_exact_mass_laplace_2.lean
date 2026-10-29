-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_cr_new_finite_killed_geometric_potential_exact_mass_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:42:29.94764+00:00
-- url     : https://prove2.me/submissions/79e18394-0124-4f1d-9527-91c567914e63

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
import Theorems.Thm_AvramDividend_Classical_additive_convolution_powers_mass
import Theorems.Thm_AvramDividend_Classical_finite_positive_geometric_measure_sum_of_mass_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_convolution_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_geometric_measure_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-- Exact total mass and raw Laplace transform of one positive killed renewal measure. -/
theorem solution (κ : Measure ℝ) [SFinite κ] (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (δ : ℝ≥0∞) (hδ : 0 < δ) (hδfin : δ ≠ ⊤)
    (hgap : κ Set.univ < δ) :
    ∃ β : Measure ℝ,
      β Set.univ = δ⁻¹ * (1 - δ⁻¹ * κ Set.univ)⁻¹ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂β) =
          δ⁻¹ * (1 - δ⁻¹ *
            (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹ := by
  obtain ⟨m, hm0, hmsucc, hsf⟩ := exists_sfinite_convolution_power_sequence κ
  let c : ℝ≥0∞ := δ⁻¹
  have hc : 0 < c := ENNReal.inv_pos.mpr hδfin
  have hcfin : c ≠ ⊤ := (ENNReal.inv_lt_top.mpr hδ).ne
  have hcr : c * κ Set.univ < 1 := by
    change δ⁻¹ * κ Set.univ < 1
    rw [← ENNReal.div_eq_inv_mul]
    exact (ENNReal.div_lt_iff (Or.inl (ne_of_gt hδ))
      (Or.inl hδfin)).mpr (by simpa using hgap)
  let β : Measure ℝ := Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)
  have hpowmass : ∀ n : ℕ, m n Set.univ = (κ Set.univ) ^ n :=
    additive_convolution_powers_mass κ m hm0 hmsucc hsf
  have hβmass := finite_positive_geometric_measure_sum_of_mass_powers
    m c (κ Set.univ) hc hcfin hcr hpowmass
  have hsuppConv (ν : Measure ℝ) [SFinite ν] (hν : ν (Iio (0 : ℝ)) = 0) :
      (Measure.conv κ ν) (Iio (0 : ℝ)) = 0 := by
    have hset : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by
      ext a; simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
    have hx : ∀ᵐ x : ℝ ∂κ, 0 ≤ x := by
      apply (ae_iff).2
      rw [hset]
      exact hκsupp
    have hy : ∀ᵐ y : ℝ ∂ν, 0 ≤ y := by
      apply (ae_iff).2
      rw [hset]; exact hν
    have hmeas : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 + p.2} := by measurability
    have hp : ∀ᵐ p : ℝ × ℝ ∂κ.prod ν, 0 ≤ p.1 + p.2 := by
      apply (Measure.ae_prod_iff_ae_ae hmeas).2
      filter_upwards [hx] with x hxx
      filter_upwards [hy] with y hyy
      exact add_nonneg hxx hyy
    unfold Measure.conv
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
    have he := (ae_iff).mp hp
    have hs : {p : ℝ × ℝ | ¬ 0 ≤ p.1 + p.2} =
        (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iio 0 := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio, not_le]
    rw [← hs]
    exact he
  have hmsupp : ∀ n : ℕ, m n (Iio (0 : ℝ)) = 0 := by
    intro n
    induction n with
    | zero => rw [hm0]; simp
    | succ n ih =>
      letI : SFinite (m n) := hsf n
      simpa only [Nat.succ_eq_add_one, hmsucc n] using hsuppConv (m n) ih
  have hβsupp : β (Iio (0 : ℝ)) = 0 := by
    dsimp [β]
    rw [Measure.sum_apply_eq_zero]
    intro n
    rw [Measure.smul_apply, hmsupp n]
    simp
  refine ⟨β, ?_, hβsupp, ?_⟩
  · simpa only [β, c] using hβmass.1
  · intro s hs
    let r : ℝ≥0∞ := ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ
    have hp := positiveLaplace_convolution_powers κ m s r hm0 hmsucc hsf rfl
    have hβLap := positiveLaplace_geometric_measure_sum m s r c hp
    simpa only [β, c, r] using hβLap
