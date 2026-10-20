-- Prove2me | solution 1 for AvramDividend.Classical.positive_supported_renewal_measure_of_laplace_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:02:31.687898+00:00
-- url     : https://prove2.me/submissions/6a37c70d-dff3-4b33-b383-2287caaa6d8c

import Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
import Theorems.Thm_AvramDividend_Classical_positive_geometric_renewal_measure_package
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Measurability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
Independent geometric-renewal theorem.
This proof does not depend on BV scale functions, Esscher roots, or the
mission's parent theorem, and uses only previously Proved dependencies.
-/
theorem solution
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (δ r : ℝ≥0∞) (hδ : 0 < δ) (hδfin : δ ≠ ⊤) (hr : r < δ)
    (s : ℝ) (hs : 0 < s)
    (hκ : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) = r) :
    ∃ β : Measure ℝ,
      β (Iio (0 : ℝ)) = 0 ∧
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂β) =
          δ⁻¹ * (1 - δ⁻¹ * r)⁻¹ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      0 < β {0} := by
  obtain ⟨m, hm0, hmsucc, hsf⟩ :=
    exists_sfinite_convolution_power_sequence κ
  have hconvSupport (ν : Measure ℝ) [SFinite ν]
      (hν : ν (Iio (0 : ℝ)) = 0) :
      (Measure.conv κ ν) (Iio (0 : ℝ)) = 0 := by
    have hκset : κ {x : ℝ | ¬ 0 ≤ x} = 0 := by
      have hs : {x : ℝ | ¬ 0 ≤ x} = Iio (0 : ℝ) := by
        ext x
        simp
      rw [hs]
      exact hκsupp
    have hνset : ν {y : ℝ | ¬ 0 ≤ y} = 0 := by
      have hs : {y : ℝ | ¬ 0 ≤ y} = Iio (0 : ℝ) := by
        ext y
        simp
      rw [hs]
      exact hν
    have hx : ∀ᵐ x : ℝ ∂κ, 0 ≤ x := (ae_iff).2 hκset
    have hy : ∀ᵐ y : ℝ ∂ν, 0 ≤ y := (ae_iff).2 hνset
    have hmeas :
        MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 + p.2} := by
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
    | zero =>
      rw [hm0]
      simp
    | succ n ih =>
      letI : SFinite (m n) := hsf n
      have hrec : m (Nat.succ n) = Measure.conv κ (m n) := by
        simpa only [Nat.succ_eq_add_one] using hmsucc n
      rw [hrec]
      exact hconvSupport (m n) ih
  let c : ℝ≥0∞ := δ⁻¹
  have hc : 0 < c := ENNReal.inv_pos.mpr hδfin
  have hcfin : c < ⊤ := ENNReal.inv_lt_top.mpr hδ
  have hmul : c * r < 1 := by
    change δ⁻¹ * r < 1
    rw [← ENNReal.div_eq_inv_mul]
    exact (ENNReal.div_lt_iff (Or.inl (ne_of_gt hδ))
      (Or.inl hδfin)).mpr (by simpa using hr)
  have hgeom : c * (1 - c * r)⁻¹ ≠ ⊤ :=
    (ENNReal.mul_lt_top hcfin
      (ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr hmul))).ne
  let β : Measure ℝ := Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)
  have hβsupp : β (Iio (0 : ℝ)) = 0 := by
    dsimp [β]
    rw [Measure.sum_apply_eq_zero]
    intro n
    rw [Measure.smul_apply, hmsupp n]
    simp
  have hp := positive_geometric_renewal_measure_package
    κ m s r c hs hm0 hmsucc hsf hκ hc hgeom
  refine ⟨β, hβsupp, ?_, ?_, ?_⟩
  · simpa [β] using hp.1
  · simpa [β] using hp.2.1
  · simpa [β] using hp.2.2
