-- Prove2me | solution 1 for AvramDividend.Classical.positive_tilted_kernel_contractivity_of_discount_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T22:30:01.504577+00:00
-- url     : https://prove2.me/submissions/c08556d6-d628-40bc-a4f9-47c638eac190

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ≥0)
    (δ q t : ℝ)
    (hδ : 0 < δ) (hq : 0 < q) (ht : 0 < t)
    (hsmall :
      ENNReal.ofReal (q / t) +
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal
              ((1 - Real.exp (-t * (z : ℝ))) / t) ∂μ)
        < ENNReal.ofReal δ) :
    let a : ℝ := q / δ
    let s : ℝ := t - a
    0 < s ∧
      (∫⁻ z : ℝ≥0,
        ENNReal.ofReal
          ((1 - Real.exp (-(s + a) * (z : ℝ))) / s) ∂μ)
        < ENNReal.ofReal δ := by
  dsimp
  let J : ℝ≥0∞ :=
    ∫⁻ z : ℝ≥0,
      ENNReal.ofReal
        ((1 - Real.exp (-t * (z : ℝ))) / t) ∂μ
  change ENNReal.ofReal (q / t) + J < ENNReal.ofReal δ at hsmall
  have hsum_ne : ENNReal.ofReal (q / t) + J ≠ ∞ :=
    ne_top_of_lt hsmall
  have hJ_ne : J ≠ ∞ := by
    intro hJ
    apply hsum_ne
    simp [hJ]
  have hreal : q / t + J.toReal < δ := by
    have h :=
      (ENNReal.toReal_lt_toReal hsum_ne ENNReal.ofReal_ne_top).2 hsmall
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hJ_ne,
      ENNReal.toReal_ofReal (div_nonneg hq.le ht.le),
      ENNReal.toReal_ofReal hδ.le] at h
    exact h
  have hqt : q / t < δ := by
    have hJnonneg : 0 ≤ J.toReal := ENNReal.toReal_nonneg
    linarith
  have ha_lt_t : q / δ < t := by
    apply (div_lt_iff₀ hδ).2
    have hq_lt : q < δ * t := (div_lt_iff₀ ht).1 hqt
    simpa [mul_comm] using hq_lt
  have hs : 0 < t - q / δ :=
    sub_pos.mpr ha_lt_t
  refine ⟨hs, ?_⟩
  have hJreal : J.toReal < δ - q / t := by
    linarith
  have hfac_pos : 0 < t / (t - q / δ) :=
    div_pos ht hs
  have hfac_nonneg : 0 ≤ t / (t - q / δ) :=
    hfac_pos.le
  have hscaledReal :
      (t / (t - q / δ)) * J.toReal < δ := by
    have h :=
      mul_lt_mul_of_pos_left hJreal hfac_pos
    have hqtd : q < t * δ := by
      have h := (div_lt_iff₀ ht).1 hqt
      simpa [mul_comm] using h
    have hden : t * δ - q ≠ 0 :=
      ne_of_gt (sub_pos.mpr hqtd)
    have halg :
        (t / (t - q / δ)) * (δ - q / t) = δ := by
      field_simp [ht.ne', hδ.ne', hs.ne', hden]
      <;> ring
    rwa [halg] at h
  have hscale :
      (∫⁻ z : ℝ≥0,
        ENNReal.ofReal
          ((1 - Real.exp
            (-((t - q / δ) + q / δ) * (z : ℝ))) /
              (t - q / δ)) ∂μ) =
        ENNReal.ofReal (t / (t - q / δ)) * J := by
    rw [← lintegral_const_mul'
      (μ := μ)
      (ENNReal.ofReal (t / (t - q / δ)))
      (fun z : ℝ≥0 =>
        ENNReal.ofReal
          ((1 - Real.exp (-t * (z : ℝ))) / t))
      ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro z
    rw [← ENNReal.ofReal_mul hfac_nonneg]
    congr 1
    have hsum : (t - q / δ) + q / δ = t := by
      ring
    rw [hsum]
    field_simp [ht.ne', hs.ne']
  rw [hscale]
  have hprod_ne :
      ENNReal.ofReal (t / (t - q / δ)) * J ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ_ne
  apply (ENNReal.lt_ofReal_iff_toReal_lt hprod_ne).2
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hfac_nonneg]
  exact hscaledReal
