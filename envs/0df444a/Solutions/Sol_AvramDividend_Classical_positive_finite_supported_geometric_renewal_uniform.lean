-- Prove2me | solution 1 for AvramDividend.Classical.positive_finite_supported_geometric_renewal_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:30:46.265754+00:00
-- url     : https://prove2.me/submissions/52ac4b53-369e-4eea-a704-c4dd2c72e619

import Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
import Theorems.Thm_AvramDividend_Classical_additive_convolution_powers_mass
import Theorems.Thm_AvramDividend_Classical_finite_positive_geometric_measure_sum_of_mass_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_convolution_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_geometric_measure_sum
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Measurability
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
Independent fixed geometric renewal measure valid for all s>0.
Targeted Mathlib imports, no Open theorem imports.
-/
theorem solution
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (δ : ℝ≥0∞) (hδ : 0 < δ) (hδfin : δ ≠ ⊤)
    (hgap : κ Set.univ < δ) :
    ∃ β : Measure ℝ,
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          (δ⁻¹ * (1 - δ⁻¹ *
            (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹)) := by
  obtain ⟨m, hm0, hmsucc, hsf⟩ :=
    exists_sfinite_convolution_power_sequence κ
  have hconvSupport (ν : Measure ℝ) [SFinite ν]
      (hν : ν (Iio (0 : ℝ)) = 0) :
      (Measure.conv κ ν) (Iio (0 : ℝ)) = 0 := by
    have hκset : κ {x : ℝ | ¬ 0 ≤ x} = 0 := by
      have hs : {x : ℝ | ¬ 0 ≤ x} = Iio (0 : ℝ) := by ext x; simp
      rw [hs]; exact hκsupp
    have hνset : ν {y : ℝ | ¬ 0 ≤ y} = 0 := by
      have hs : {y : ℝ | ¬ 0 ≤ y} = Iio (0 : ℝ) := by ext y; simp
      rw [hs]; exact hν
    have hx : ∀ᵐ x : ℝ ∂κ, 0 ≤ x := (ae_iff).2 hκset
    have hy : ∀ᵐ y : ℝ ∂ν, 0 ≤ y := (ae_iff).2 hνset
    have hmeas : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 + p.2} := by
      measurability
    have hp : ∀ᵐ p : ℝ × ℝ ∂κ.prod ν, 0 ≤ p.1 + p.2 := by
      apply (Measure.ae_prod_iff_ae_ae hmeas).2
      filter_upwards [hx] with x hx'
      filter_upwards [hy] with y hy'
      exact add_nonneg hx' hy'
    unfold Measure.conv
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
    have hnull : (κ.prod ν) {p : ℝ × ℝ | p.1 + p.2 < 0} = 0 := by
      have hn := (ae_iff).mp hp
      simpa only [not_le] using hn
    exact hnull
  have hmsupp : ∀ n : ℕ, m n (Iio (0 : ℝ)) = 0 := by
    intro n
    induction n with
    | zero => rw [hm0]; simp
    | succ n ih =>
      letI : SFinite (m n) := hsf n
      have hrec : m (Nat.succ n) = Measure.conv κ (m n) := by
        simpa only [Nat.succ_eq_add_one] using hmsucc n
      rw [hrec]
      exact hconvSupport (m n) ih
  let c : ℝ≥0∞ := δ⁻¹
  have hc : 0 < c := ENNReal.inv_pos.mpr hδfin
  have hcfin : c ≠ ⊤ := (ENNReal.inv_lt_top.mpr hδ).ne
  have hcr : c * κ Set.univ < 1 := by
    change δ⁻¹ * κ Set.univ < 1
    rw [← ENNReal.div_eq_inv_mul]
    exact (ENNReal.div_lt_iff (Or.inl (ne_of_gt hδ))
      (Or.inl hδfin)).mpr (by simpa using hgap)
  let β : Measure ℝ := Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)
  have hm : ∀ n : ℕ, m n Set.univ = (κ Set.univ) ^ n :=
    additive_convolution_powers_mass κ m hm0 hmsucc hsf
  have hfinite := finite_positive_geometric_measure_sum_of_mass_powers
    m c (κ Set.univ) hc hcfin hcr hm
  have hβsupp : β (Iio (0 : ℝ)) = 0 := by
    dsimp [β]
    rw [Measure.sum_apply_eq_zero]
    intro n
    rw [Measure.smul_apply, hmsupp n]
    simp
  letI : SFinite β := by dsimp [β]; infer_instance
  have hlocal (x : ℝ) : β (Iic x) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite.2.2 (measure_mono (subset_univ (Iic x)))
  refine ⟨β, hfinite.2.1, hfinite.2.2, hβsupp, hlocal, ?_⟩
  intro s hs
  let r : ℝ≥0∞ := ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ
  have hpow := positiveLaplace_convolution_powers κ m s r hm0 hmsucc hsf rfl
  have hβLap := positiveLaplace_geometric_measure_sum m s r c hpow
  have hcum := positiveLaplace_cumulative_measure β s hs hβsupp
  rw [show (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂β) =
    c * (1 - c * r)⁻¹ by simpa [β] using hβLap] at hcum
  simpa only [c, r] using hcum
