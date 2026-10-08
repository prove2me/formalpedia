-- Prove2me | solution 1 for AvramDividend.Classical.bv_fixed_renewal_cumulative_positiveLaplace_canonical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:47:05.224001+00:00
-- url     : https://prove2.me/submissions/2eb1a670-9885-4156-ba50-084dac7cfafe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
import Theorems.Thm_AvramDividend_Classical_bv_supported_positive_kernel_transform_gap
import Theorems.Thm_AvramDividend_Classical_positive_geometric_renewal_measure_package
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_convolution_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_geometric_measure_sum
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (β : Measure ℝ) (b : ℝ), (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧ 0 < β {0} ∧
      ∀ s : ℝ, b ≤ s →
        (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) * ((ENNReal.ofReal X.drift)⁻¹ *
          (1 - (ENNReal.ofReal X.drift)⁻¹ * (∫⁻ z : ℝ≥0, ENNReal.ofReal
            ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))))⁻¹) := by
  have hδ : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  obtain ⟨κ, hκsf, hκsupp, hκLap, ⟨b, hb, hgap⟩⟩ :=
    bv_supported_positive_kernel_transform_gap X hX hbv q hq
  letI : SFinite κ := hκsf
  obtain ⟨m, hm0, hmsucc, hsf⟩ :=
    exists_sfinite_convolution_power_sequence κ
  have hconvSupport (ν : Measure ℝ) [SFinite ν] (hν : ν (Iio (0 : ℝ)) = 0) :
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
  let δe : ℝ≥0∞ := ENNReal.ofReal X.drift
  let c : ℝ≥0∞ := δe⁻¹
  have hδe0 : 0 < δe := ENNReal.ofReal_pos.mpr hδ
  have hδefin : δe ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : 0 < c := ENNReal.inv_pos.mpr hδefin
  have hcfin : c < ⊤ := ENNReal.inv_lt_top.mpr hδe0
  let r₀ : ℝ≥0∞ := ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-b * x)) ∂κ
  have hgeom : c * (1 - c * r₀)⁻¹ ≠ ⊤ := by
    have hmul : c * r₀ < 1 := by
      calc c * r₀ < c * δe :=
          ENNReal.mul_lt_mul_right (ne_of_gt hc) (ne_of_lt hcfin) hgap
        _ = 1 := ENNReal.inv_mul_cancel (ne_of_gt hδe0) hδefin
    exact (ENNReal.mul_lt_top hcfin
      (ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr hmul))).ne
  let β : Measure ℝ := Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)
  letI : ∀ n : ℕ, SFinite (m n) := hsf
  letI : SFinite β := by dsimp [β]; infer_instance
  have hβsupp : β (Iio (0 : ℝ)) = 0 := by
    dsimp [β]
    rw [Measure.sum_apply_eq_zero]
    intro n
    rw [Measure.smul_apply, hmsupp n]
    simp
  have hpack : (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧ 0 < β {0} := by
    have hp := positive_geometric_renewal_measure_package
      κ m b r₀ c hb hm0 hmsucc hsf rfl hc hgeom
    simpa [β] using hp.2
  refine ⟨β, b, hpack.1, hpack.2, ?_⟩
  intro s hs
  have hspos : 0 < s := lt_of_lt_of_le hb hs
  let r : ℝ≥0∞ := ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ
  have hmLap := positiveLaplace_convolution_powers κ m s r hm0 hmsucc hsf rfl
  have hβLap : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂β) =
      c * (1 - c * r)⁻¹ := by
    simpa [β] using positiveLaplace_geometric_measure_sum m s r c hmLap
  have hcum := positiveLaplace_cumulative_measure β s hspos hβsupp
  rw [hβLap] at hcum
  have hk := hκLap s hspos
  dsimp [r] at hcum
  rw [hk] at hcum
  simpa [c, δe] using hcum
