-- Prove2me | solution 1 for EntropicBarrier.Universal.lemma2_third_moment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T03:58:48.590979+00:00
-- url     : https://prove2.me/submissions/1fb33211-e29e-4400-94ea-18e00544bcfa

import Mathlib
import Definitions.Def_LogConcaveOn

set_option autoImplicit false

open scoped RealInnerProductSpace Nat
open MeasureTheory Filter

namespace L2TM

/-- Polynomial moments of a function with integrable moments up to order three. -/
theorem int_poly (f : ℝ → ℝ) (h0 : Integrable f) (h1 : Integrable fun x => x * f x)
    (h2 : Integrable fun x => x ^ 2 * f x) (h3 : Integrable fun x => x ^ 3 * f x)
    (c3 c2 c1 c0 : ℝ) :
    Integrable (fun x => (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * f x) ∧
    ∫ x, (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * f x =
      c3 * (∫ x, x ^ 3 * f x) + c2 * (∫ x, x ^ 2 * f x) + c1 * (∫ x, x * f x) +
        c0 * (∫ x, f x) := by
  have e : (fun x => (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * f x) =
      fun x => ((c3 * (x ^ 3 * f x) + c2 * (x ^ 2 * f x)) + c1 * (x * f x)) + c0 * f x := by
    ext x; ring
  have i3 := h3.const_mul c3
  have i2 := h2.const_mul c2
  have i1 := h1.const_mul c1
  have i0 := h0.const_mul c0
  have i32 : Integrable (fun x => c3 * (x ^ 3 * f x) + c2 * (x ^ 2 * f x)) := i3.add i2
  have i321 : Integrable (fun x => c3 * (x ^ 3 * f x) + c2 * (x ^ 2 * f x) + c1 * (x * f x)) :=
    i32.add i1
  rw [e]
  refine ⟨i321.add i0, ?_⟩
  rw [integral_add i321 i0, integral_add i32 i1, integral_add i3 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

theorem pow_bound (t : ℝ) (ht : 0 ≤ t) : t ≤ 1 + t ^ 3 ∧ t ^ 2 ≤ 1 + t ^ 3 := by
  rcases le_total t 1 with h | h
  · constructor <;> nlinarith [pow_nonneg ht 3, mul_nonneg ht (sub_nonneg.2 h)]
  · constructor <;> nlinarith [pow_nonneg ht 3, mul_nonneg ht (sub_nonneg.2 h),
      mul_nonneg (mul_nonneg ht ht) (sub_nonneg.2 h)]

theorem int_low (f : ℝ → ℝ) (h0 : Integrable f) (h3 : Integrable fun x => x ^ 3 * f x) :
    (Integrable fun x => x * f x) ∧ (Integrable fun x => x ^ 2 * f x) := by
  have hm := h0.aestronglyMeasurable
  have hb := h0.norm.add h3.norm
  constructor
  · refine Integrable.mono' hb (continuous_id.aestronglyMeasurable.mul hm)
      (Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_pow, Pi.add_apply, id_eq]
    have := (pow_bound |x| (abs_nonneg x)).1
    nlinarith [abs_nonneg (f x)]
  · refine Integrable.mono' hb ((continuous_pow 2).aestronglyMeasurable.mul hm)
      (Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_pow, Pi.add_apply]
    have := (pow_bound |x| (abs_nonneg x)).2
    nlinarith [abs_nonneg (f x)]

/-- The exponential density with mean `σ`, supported on `(0, ∞)`. -/
noncomputable def qq (σ : ℝ) (y : ℝ) : ℝ :=
  Set.indicator (Set.Ioi 0) (fun y => σ⁻¹ * Real.exp (-(σ⁻¹ * y))) y

theorem qq_nonneg (σ : ℝ) (hσ : 0 < σ) (y : ℝ) : 0 ≤ qq σ y := by
  unfold qq
  exact Set.indicator_nonneg (fun y _ => by positivity) y

theorem qq_moment (σ : ℝ) (hσ : 0 < σ) (j : ℕ) : ∫ y, y ^ j * qq σ y = σ ^ j * j ! := by
  have e : ∀ y : ℝ, y ^ j * qq σ y = Set.indicator (Set.Ioi 0)
      (fun y => σ⁻¹ * (y ^ (((j : ℝ) + 1) - 1) * Real.exp (-(σ⁻¹ * y)))) y := by
    intro y
    unfold qq
    by_cases hy : y ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, add_sub_cancel_right,
        Real.rpow_natCast]
      ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [integral_congr_ae (Eventually.of_forall e), integral_indicator measurableSet_Ioi,
    integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) (inv_pos.2 hσ),
    Real.Gamma_nat_eq_factorial, one_div, inv_inv, ← Nat.cast_succ, Real.rpow_natCast, pow_succ]
  field_simp

theorem qq_int (σ : ℝ) (hσ : 0 < σ) (j : ℕ) : Integrable fun y => y ^ j * qq σ y :=
  Integrable.of_integral_ne_zero (by rw [qq_moment σ hσ j]; positivity)

theorem qq_poly (σ : ℝ) (hσ : 0 < σ) (c3 c2 c1 c0 : ℝ) :
    Integrable (fun y => (c3 * y ^ 3 + c2 * y ^ 2 + c1 * y + c0) * qq σ y) ∧
    ∫ y, (c3 * y ^ 3 + c2 * y ^ 2 + c1 * y + c0) * qq σ y =
      c3 * (6 * σ ^ 3) + c2 * (2 * σ ^ 2) + c1 * σ + c0 := by
  have h0 : Integrable (qq σ) := by simpa using qq_int σ hσ 0
  have h1 : Integrable fun y => y * qq σ y := by simpa using qq_int σ hσ 1
  obtain ⟨hi, he⟩ := int_poly (qq σ) h0 h1 (qq_int σ hσ 2) (qq_int σ hσ 3) c3 c2 c1 c0
  refine ⟨hi, ?_⟩
  have m0 : ∫ y, qq σ y = 1 := by simpa using qq_moment σ hσ 0
  have m1 : ∫ y, y * qq σ y = σ := by simpa using qq_moment σ hσ 1
  have m2 := qq_moment σ hσ 2
  have m3 := qq_moment σ hσ 3
  norm_num [Nat.factorial] at m2 m3
  rw [he]
  linear_combination c3 * m3 + c2 * m2 + c1 * m1 + c0 * m0

/-- Moments of the shifted exponential `q x = qq σ (x + σ)` (mean zero, variance `σ²`). -/
theorem q_poly (σ : ℝ) (hσ : 0 < σ) (c3 c2 c1 c0 : ℝ) :
    Integrable (fun x => (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * qq σ (x + σ)) ∧
    ∫ x, (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * qq σ (x + σ) =
      c3 * (2 * σ ^ 3) + c2 * σ ^ 2 + c0 := by
  obtain ⟨hi, he⟩ := qq_poly σ hσ c3 (-3 * σ * c3 + c2) (3 * σ ^ 2 * c3 - 2 * σ * c2 + c1)
    (-σ ^ 3 * c3 + σ ^ 2 * c2 - σ * c1 + c0)
  have key : ∀ x : ℝ, (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * qq σ (x + σ) =
      (c3 * (x + σ) ^ 3 + (-3 * σ * c3 + c2) * (x + σ) ^ 2 +
        (3 * σ ^ 2 * c3 - 2 * σ * c2 + c1) * (x + σ)
        + (-σ ^ 3 * c3 + σ ^ 2 * c2 - σ * c1 + c0)) * qq σ (x + σ) := by
    intro x; ring
  have hshift := integral_add_right_eq_self (μ := volume) (fun y => (c3 * y ^ 3 +
    (-3 * σ * c3 + c2) * y ^ 2 + (3 * σ ^ 2 * c3 - 2 * σ * c2 + c1) * y
        + (-σ ^ 3 * c3 + σ ^ 2 * c2 - σ * c1 + c0)) * qq σ y) σ
  refine ⟨(hi.comp_add_right σ).congr (Eventually.of_forall fun x => (key x).symm), ?_⟩
  rw [integral_congr_ae (Eventually.of_forall key), hshift, he]
  ring

end L2TM

theorem solution (dens : ℝ → ℝ)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ dens)
    (hprob : ∫ x, dens x = 1) (hcenter : ∫ x, x * dens x = 0) :
    ∫ x, x ^ 3 * dens x ≤ 2 * (∫ x, x ^ 2 * dens x) ^ ((3 : ℝ) / 2) := by
  have hnn : ∀ x, 0 ≤ dens x := fun x => hlc.1 x (Set.mem_univ x)
  have hm2nn : 0 ≤ ∫ x, x ^ 2 * dens x :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg x) (hnn x)
  by_cases h3 : Integrable fun x => x ^ 3 * dens x
  swap
  · rw [integral_undef h3]; positivity
  have h0 : Integrable dens := Integrable.of_integral_ne_zero (by rw [hprob]; norm_num)
  obtain ⟨h1, h2⟩ := L2TM.int_low dens h0 h3
  set m2 := ∫ x, x ^ 2 * dens x with hm2
  have hm2pos : 0 < m2 := by
    rcases hm2nn.lt_or_eq with h | h
    · exact h
    exfalso
    have hz : (fun x => x ^ 2 * dens x) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (sq_nonneg x) (hnn x)) h2).1 h.symm
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 :=
      (measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℝ))).mono fun x hx => hx
    have hd : dens =ᵐ[volume] 0 := (hz.and hne).mono fun x hx => by
      have hx1 : x ^ 2 * dens x = 0 := hx.1
      rcases mul_eq_zero.1 hx1 with h' | h'
      · exact absurd ((pow_eq_zero_iff two_ne_zero).1 h') hx.2
      · exact h'
    have := integral_congr_ae hd
    rw [hprob] at this
    simp at this
  set σ := Real.sqrt m2 with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hm2pos
  have hσ2 : σ ^ 2 = m2 := Real.sq_sqrt hm2pos.le
  have hσ3 : m2 ^ ((3 : ℝ) / 2) = σ ^ 3 := by
    rw [hσdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hm2pos.le]
    norm_num
  rw [hσ3]
  -- the comparison density
  set q : ℝ → ℝ := fun x => L2TM.qq σ (x + σ) with hqdef
  have hq_nn : ∀ x, 0 ≤ q x := fun x => L2TM.qq_nonneg σ hσ _
  have hq_left : ∀ x, x ≤ -σ → q x = 0 := by
    intro x hx
    simp only [hqdef, L2TM.qq]
    exact Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; linarith) _
  have hq_right : ∀ x, -σ < x → q x = σ⁻¹ * Real.exp (-(σ⁻¹ * (x + σ))) := by
    intro x hx
    simp only [hqdef, L2TM.qq]
    exact Set.indicator_of_mem (by simp only [Set.mem_Ioi]; linarith) _
  -- the interval property of `{q ≤ dens}` on `(-σ, ∞)`
  have hinterval : ∀ x y z, -σ < x → x < y → y < z → q x ≤ dens x → q z ≤ dens z →
      q y ≤ dens y := by
    intro x y z hx hxy hyz hqx hqz
    have hne : z - x ≠ 0 := by linarith
    have hpos : 0 < z - x := by linarith
    set a := (z - y) / (z - x) with ha
    set b := (y - x) / (z - x) with hb
    have ha0 : 0 ≤ a := div_nonneg (by linarith) hpos.le
    have hb0 : 0 ≤ b := div_nonneg (by linarith) hpos.le
    have hab : a + b = 1 := by
      rw [ha, hb, ← add_div, div_eq_one_iff_eq hne]; ring
    have hcomb : a • x + b • z = y := by
      rw [smul_eq_mul, smul_eq_mul, ha, hb, div_mul_eq_mul_div, div_mul_eq_mul_div,
        ← add_div, div_eq_iff hne]
      ring
    have hl := hlc.2 x (Set.mem_univ x) z (Set.mem_univ z) a b ha0 hb0 hab
    rw [hcomb] at hl
    have hqy : q y = q x ^ a * q z ^ b := by
      rw [hq_right x hx, hq_right y (by linarith), hq_right z (by linarith),
        Real.mul_rpow (inv_nonneg.2 hσ.le) (Real.exp_pos _).le,
        Real.mul_rpow (inv_nonneg.2 hσ.le) (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_mul]
      have hexp : -(σ⁻¹ * (x + σ)) * a + -(σ⁻¹ * (z + σ)) * b = -(σ⁻¹ * (y + σ)) := by
        rw [← hcomb, smul_eq_mul, smul_eq_mul]
        linear_combination (-(σ⁻¹ * σ)) * hab
      calc σ⁻¹ * Real.exp (-(σ⁻¹ * (y + σ)))
          = σ⁻¹ ^ (a + b) * Real.exp (-(σ⁻¹ * (x + σ)) * a + -(σ⁻¹ * (z + σ)) * b) := by
            rw [hab, Real.rpow_one, hexp]
        _ = _ := by rw [Real.rpow_add (inv_pos.2 hσ), Real.exp_add]; ring
    rw [hqy]
    refine le_trans ?_ hl
    exact mul_le_mul (Real.rpow_le_rpow (hq_nn x) hqx ha0) (Real.rpow_le_rpow (hq_nn z) hqz hb0)
      (Real.rpow_nonneg (hq_nn z) _) (Real.rpow_nonneg (hnn x) _)
  -- the moment identity for `dens - q`
  have hE : ∀ c3 c2 c1 c0 : ℝ,
      Integrable (fun x => (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * (dens x - q x)) ∧
      ∫ x, (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * (dens x - q x) =
        c3 * ((∫ x, x ^ 3 * dens x) - 2 * σ ^ 3) := by
    intro c3 c2 c1 c0
    obtain ⟨hi1, he1⟩ := L2TM.int_poly dens h0 h1 h2 h3 c3 c2 c1 c0
    obtain ⟨hi2, he2⟩ := L2TM.q_poly σ hσ c3 c2 c1 c0
    have e : (fun x => (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * (dens x - q x)) =
        fun x => (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * dens x -
          (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0) * L2TM.qq σ (x + σ) := by
      ext x; simp only [hqdef]; ring
    rw [e]
    refine ⟨hi1.sub hi2, ?_⟩
    rw [integral_sub hi1 hi2, he1, he2, hcenter, hprob, ← hm2, ← hσ2]
    ring
  -- case A: three sign changes
  have caseA : ∀ a0 b0 : ℝ, -σ ≤ a0 → a0 ≤ b0 →
      (∀ x, -σ < x → x < a0 → dens x ≤ q x) → (∀ x, a0 < x → x < b0 → q x ≤ dens x) →
      (∀ x, b0 < x → dens x ≤ q x) → ∫ x, x ^ 3 * dens x ≤ 2 * σ ^ 3 := by
    intro a0 b0 ha0 hab hR2 hR3 hR4
    obtain ⟨-, he⟩ := hE 1 (σ - a0 - b0) (a0 * b0 - σ * a0 - σ * b0) (σ * a0 * b0)
    have hpt : ∀ x, (1 * x ^ 3 + (σ - a0 - b0) * x ^ 2 + (a0 * b0 - σ * a0 - σ * b0) * x +
        σ * a0 * b0) * (dens x - q x) ≤ 0 := by
      intro x
      have hP : 1 * x ^ 3 + (σ - a0 - b0) * x ^ 2 + (a0 * b0 - σ * a0 - σ * b0) * x +
          σ * a0 * b0 = (x + σ) * (x - a0) * (x - b0) := by ring
      rw [hP]
      rcases le_or_gt x (-σ) with h1 | h1
      · have hd : 0 ≤ dens x - q x := by rw [hq_left x h1]; linarith [hnn x]
        refine mul_nonpos_of_nonpos_of_nonneg ?_ hd
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) (by linarith)
      rcases lt_or_ge x a0 with h2 | h2
      · have hd : dens x - q x ≤ 0 := by linarith [hR2 x h1 h2]
        refine mul_nonpos_of_nonneg_of_nonpos ?_ hd
        exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (by linarith)
      rcases lt_or_ge b0 x with h4 | h4
      · have hd : dens x - q x ≤ 0 := by linarith [hR4 x h4]
        refine mul_nonpos_of_nonneg_of_nonpos ?_ hd
        exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      rcases eq_or_lt_of_le h2 with h5 | h5
      · rw [show x - a0 = 0 by linarith]; simp
      rcases eq_or_lt_of_le h4 with h6 | h6
      · rw [show x - b0 = 0 by linarith]; simp
      have hd : 0 ≤ dens x - q x := by linarith [hR3 x h5 h6]
      refine mul_nonpos_of_nonpos_of_nonneg ?_ hd
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have := integral_nonpos (μ := (volume : Measure ℝ)) hpt
    rw [he] at this
    linarith
  -- case B: two sign changes (then `dens = q` a.e.)
  have caseB : ∀ a0 : ℝ, -σ ≤ a0 →
      (∀ x, -σ < x → x < a0 → dens x ≤ q x) → (∀ x, a0 < x → q x ≤ dens x) →
      ∫ x, x ^ 3 * dens x ≤ 2 * σ ^ 3 := by
    intro a0 ha0 hR2 hR3
    obtain ⟨hi, he⟩ := hE 0 1 (σ - a0) (-(σ * a0))
    have hpt : ∀ x, 0 ≤ (0 * x ^ 3 + 1 * x ^ 2 + (σ - a0) * x + -(σ * a0)) * (dens x - q x) := by
      intro x
      have hP : 0 * x ^ 3 + 1 * x ^ 2 + (σ - a0) * x + -(σ * a0) = (x + σ) * (x - a0) := by ring
      rw [hP]
      rcases le_or_gt x (-σ) with h1 | h1
      · have hd : 0 ≤ dens x - q x := by rw [hq_left x h1]; linarith [hnn x]
        exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) hd
      rcases lt_or_ge x a0 with h2 | h2
      · have hd : dens x - q x ≤ 0 := by linarith [hR2 x h1 h2]
        exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) hd
      rcases eq_or_lt_of_le h2 with h5 | h5
      · rw [show x - a0 = 0 by linarith]; simp
      have hd : 0 ≤ dens x - q x := by linarith [hR3 x h5]
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hd
    have hz := (integral_eq_zero_iff_of_nonneg hpt hi).1 (by rw [he]; ring)
    obtain ⟨-, he3⟩ := hE 1 (σ - a0) (-(σ * a0)) 0
    have hz3 : (fun x => (1 * x ^ 3 + (σ - a0) * x ^ 2 + -(σ * a0) * x + 0) * (dens x - q x))
        =ᵐ[volume] 0 := hz.mono fun x hx => by
      have hx' : (0 * x ^ 3 + 1 * x ^ 2 + (σ - a0) * x + -(σ * a0)) * (dens x - q x) = 0 := hx
      simp only [Pi.zero_apply]
      linear_combination x * hx'
    have := integral_congr_ae hz3
    simp only [Pi.zero_apply, integral_zero] at this
    rw [he3] at this
    linarith
  -- split on the shape of `S = {x > -σ | q x ≤ dens x}`
  set S : Set ℝ := {x | -σ < x ∧ q x ≤ dens x} with hSdef
  have hbb : BddBelow S := ⟨-σ, fun x hx => hx.1.le⟩
  by_cases hS : S.Nonempty
  · have ha0 : -σ ≤ sInf S := le_csInf hS fun x hx => hx.1.le
    have hR2 : ∀ x, -σ < x → x < sInf S → dens x ≤ q x := by
      intro x hx1 hx2
      by_contra hc
      push Not at hc
      have := csInf_le hbb ⟨hx1, hc.le⟩
      linarith
    by_cases hB : BddAbove S
    · refine caseA (sInf S) (sSup S) ha0 (csInf_le_csSup hS hbb hB) hR2 ?_ ?_
      · intro x hx1 hx2
        obtain ⟨s1, hs1, h1⟩ := exists_lt_of_csInf_lt hS hx1
        obtain ⟨s2, hs2, h2⟩ := exists_lt_of_lt_csSup hS hx2
        exact hinterval s1 x s2 hs1.1 h1 h2 hs1.2 hs2.2
      · intro x hx
        by_contra hc
        push Not at hc
        have hx1 : -σ < x := by linarith [csInf_le_csSup hS hbb hB]
        have := le_csSup hB ⟨hx1, hc.le⟩
        linarith
    · refine caseB (sInf S) ha0 hR2 ?_
      intro x hx1
      obtain ⟨s1, hs1, h1⟩ := exists_lt_of_csInf_lt hS hx1
      obtain ⟨s2, hs2, h2⟩ : ∃ s2 ∈ S, x < s2 := by
        by_contra hc
        push Not at hc
        exact hB ⟨x, hc⟩
      exact hinterval s1 x s2 hs1.1 h1 h2 hs1.2 hs2.2
  · refine caseA (-σ) (-σ) le_rfl le_rfl (fun x h1 h2 => by linarith) (fun x h1 h2 => by linarith) ?_
    intro x hx
    by_contra hc
    push Not at hc
    exact hS ⟨x, hx, hc.le⟩
