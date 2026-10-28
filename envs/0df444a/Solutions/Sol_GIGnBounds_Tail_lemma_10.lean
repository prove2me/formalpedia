-- Prove2me | solution 1 for GIGnBounds.Tail.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:36:22.338399+00:00
-- url     : https://prove2.me/submissions/87972056-e3ba-4a39-8d9d-ac05aed667d5

import Mathlib

open MeasureTheory ProbabilityTheory

namespace GIGnL10Aux

/-- `e^{-y} ≤ 1 - y + y²` for `y ≥ 0`. -/
lemma exp_neg_le (y : ℝ) (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 := by
  have h1 : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have hpos : 0 < y + 1 := by linarith
  rw [Real.exp_neg]
  have : (Real.exp y)⁻¹ ≤ (y + 1)⁻¹ := inv_anti₀ hpos h1
  refine this.trans ?_
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith [pow_nonneg hy 3]

lemma integrable_exp (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0)
    (a b : ℝ) (ha : 0 ≤ a) : Integrable (fun z => Real.exp (a * (b - z))) ν := by
  have hae : ∀ᵐ z ∂ν, 0 ≤ z := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hν0
  refine Integrable.mono' (integrable_const (Real.exp (a * b))) ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).aestronglyMeasurable
  · filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith

lemma core (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0)
    (hν1 : ∫ z, z ∂ν = 1) (hI1 : Integrable (fun z : ℝ => z) ν)
    (hI2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (t c : ℝ) (ht : 0 < t) (htm : t * ∫ w, w ^ 2 ∂ν ≤ 1 - c) :
    ∫ z, Real.exp (t * (c - z)) ∂ν ≤ 1 := by
  have hae : ∀ᵐ z ∂ν, 0 ≤ z := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hν0
  set m2 := ∫ w, w ^ 2 ∂ν
  have hpt : ∀ᵐ z ∂ν, Real.exp (t * (c - z)) ≤
      Real.exp (t * c) * (1 - t * z + t ^ 2 * z ^ 2) := by
    filter_upwards [hae] with z hz
    have := exp_neg_le (t * z) (mul_nonneg ht.le hz)
    have he : Real.exp (t * (c - z)) = Real.exp (t * c) * Real.exp (-(t * z)) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    nlinarith
  have hint : Integrable (fun z => Real.exp (t * c) * (1 - t * z + t ^ 2 * z ^ 2)) ν := by
    exact ((integrable_const 1).sub (hI1.const_mul t) |>.add (hI2.const_mul (t ^ 2))).const_mul _
  have h1 : ∫ z, Real.exp (t * (c - z)) ∂ν ≤
      ∫ z, Real.exp (t * c) * (1 - t * z + t ^ 2 * z ^ 2) ∂ν :=
    integral_mono_ae (integrable_exp ν hν0 t c ht.le) hint hpt
  have h2 : ∫ z, Real.exp (t * c) * (1 - t * z + t ^ 2 * z ^ 2) ∂ν =
      Real.exp (t * c) * (1 - t + t ^ 2 * m2) := by
    rw [integral_const_mul]
    congr 1
    have i1 : Integrable (fun a : ℝ => 1 - t * a) ν := (integrable_const 1).sub (hI1.const_mul t)
    have i2 : Integrable (fun a : ℝ => t ^ 2 * a ^ 2) ν := hI2.const_mul (t ^ 2)
    have e1 : ∫ a, (1 - t * a + t ^ 2 * a ^ 2) ∂ν = ∫ a, (1 - t * a) ∂ν + ∫ a, t ^ 2 * a ^ 2 ∂ν :=
      integral_add i1 i2
    have e2 : ∫ a, (1 - t * a) ∂ν = ∫ a, (1 : ℝ) ∂ν - ∫ a, t * a ∂ν :=
      integral_sub (integrable_const 1) (hI1.const_mul t)
    rw [e1, e2, integral_const_mul, integral_const_mul, hν1]
    simp [m2]
  rw [h2] at h1
  refine h1.trans ?_
  have h3 : 1 - t + t ^ 2 * m2 ≤ Real.exp (-t + t ^ 2 * m2) := by
    have := Real.add_one_le_exp (-t + t ^ 2 * m2); linarith
  calc Real.exp (t * c) * (1 - t + t ^ 2 * m2)
      ≤ Real.exp (t * c) * Real.exp (-t + t ^ 2 * m2) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = Real.exp (t * (c - 1 + t * m2)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ 1 := by
        rw [Real.exp_le_one_iff]
        apply mul_nonpos_of_nonneg_of_nonpos ht.le
        linarith

end GIGnL10Aux

open GIGnL10Aux in
theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0)
    (hν1 : ∫ z, z ∂ν = 1) (hν2 : ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂ν < ⊤)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∫ z, Real.exp ((1 - c) / (11 * c * ∫ w, w ^ 2 ∂ν) * (c - z)) ∂ν ≤ 1 := by
  have hae : ∀ᵐ z ∂ν, 0 ≤ z := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hν0
  have hI1 : Integrable (fun z : ℝ => z) ν := by
    by_contra h
    rw [integral_undef h] at hν1
    norm_num at hν1
  have hI2 : Integrable (fun z : ℝ => z ^ 2) ν := by
    refine ⟨(continuous_pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => sq_nonneg z))]
    exact hν2
  set m2 := ∫ w, w ^ 2 ∂ν with hm2
  -- `m2 ≥ 1` since `z ≤ (1 + z²)/2`.
  have hm2ge : 1 ≤ m2 := by
    have : ∫ z, z ∂ν ≤ ∫ z, (1 + z ^ 2) / 2 ∂ν := by
      have i3 : Integrable (fun z : ℝ => (1 + z ^ 2) / 2) ν :=
        ((integrable_const 1).add hI2).div_const 2
      apply integral_mono hI1 i3
      intro z; simp only; nlinarith [sq_nonneg (z - 1)]
    have e3 : ∫ z, (1 + z ^ 2) ∂ν = ∫ z, (1 : ℝ) ∂ν + ∫ z, z ^ 2 ∂ν :=
      integral_add (integrable_const 1) hI2
    rw [integral_div, e3, hν1] at this
    simp at this
    linarith
  have hm2pos : 0 < m2 := by linarith
  set θ := (1 - c) / (11 * c * m2) with hθ
  have hθpos : 0 < θ := by
    apply div_pos (by linarith); positivity
  have hθm : θ * m2 = (1 - c) / (11 * c) := by
    rw [hθ]; field_simp
  by_cases hc : 1 / 2 ≤ c
  · apply core ν hν0 hν1 hI1 hI2 θ c hθpos
    rw [hθm, div_le_iff₀ (by positivity)]
    nlinarith
  · push Not at hc
    have hmono : ∫ z, Real.exp (θ * (c - z)) ∂ν ≤ ∫ z, Real.exp ((2 * θ * c) * (1 / 2 - z)) ∂ν := by
      apply integral_mono_ae (integrable_exp ν hν0 θ c hθpos.le)
        (integrable_exp ν hν0 (2 * θ * c) (1 / 2) (by positivity))
      filter_upwards [hae] with z hz
      apply Real.exp_le_exp.mpr
      have : θ * z * (1 - 2 * c) ≥ 0 := mul_nonneg (mul_nonneg hθpos.le hz) (by linarith)
      nlinarith
    refine hmono.trans ?_
    apply core ν hν0 hν1 hI1 hI2 (2 * θ * c) (1 / 2) (by positivity)
    have : 2 * θ * c * m2 = 2 * (1 - c) / 11 := by
      have : 2 * θ * c * m2 = 2 * c * (θ * m2) := by ring
      rw [this, hθm]; field_simp
    rw [this]
    linarith
