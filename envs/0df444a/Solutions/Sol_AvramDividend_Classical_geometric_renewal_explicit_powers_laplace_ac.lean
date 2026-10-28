-- Prove2me | solution 1 for AvramDividend.Classical.geometric_renewal_explicit_powers_laplace_ac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:18:33.381986+00:00
-- url     : https://prove2.me/submissions/0b177c90-e2a1-43b5-bdf9-a79577105079

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
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Expose the exact convolution-power sequence behind a finite BV renewal measure. -/
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
  obtain ⟨m, hm0, hmsucc, hsf⟩ :=
    exists_sfinite_convolution_power_sequence κ
  have hmsupp : ∀ n : ℕ, m n (Iio (0 : ℝ)) = 0 := by
    intro n
    induction n with
    | zero => rw [hm0]; simp
    | succ n ih =>
      letI : SFinite (m n) := hsf n
      have hrec : m (Nat.succ n) = Measure.conv κ (m n) := by
        simpa only [Nat.succ_eq_add_one] using hmsucc n
      rw [hrec]
      exact nonnegative_halfline_support_of_measure_convolution κ (m n) hκsupp ih
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
  have hβac : β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) :=
    geometric_convolution_renewal_positive_part_ac κ hκac m hm0 hmsucc hsf c
  letI : SFinite β := by dsimp [β]; infer_instance
  have hlocal (x : ℝ) : β (Iic x) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite.2.2 (measure_mono (subset_univ (Iic x)))
  refine ⟨m, β, hm0, hmsucc, hsf, rfl, hfinite.2.1,
    hfinite.2.2, hβsupp, hβac, hlocal, ?_⟩
  intro s hs
  let r : ℝ≥0∞ := ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ
  have hpow := positiveLaplace_convolution_powers κ m s r hm0 hmsucc hsf rfl
  have hβLap := positiveLaplace_geometric_measure_sum m s r c hpow
  have hcum := positiveLaplace_cumulative_measure β s hs hβsupp
  rw [show (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂β) =
    c * (1 - c * r)⁻¹ by simpa [β] using hβLap] at hcum
  simpa only [c, r] using hcum