-- Prove2me | solution 1 for FreedmanTail.Laplace.ineq_3_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:37:12.959993+00:00
-- url     : https://prove2.me/submissions/a8c1f70a-28c5-406f-8494-3fbb745d6142

import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents

open MeasureTheory ProbabilityTheory


namespace FreedmanTail.Laplace

/-! ### Real-analysis lemmas -/

/-- `∫_0^1 (1 - t) e^{t y} dt = (e^y - 1 - y) / y²` for `y ≠ 0`. -/
lemma G_integral (y : ℝ) (hy : y ≠ 0) :
    ∫ t in (0:ℝ)..1, (1 - t) * Real.exp (t * y) = (Real.exp y - 1 - y) / y ^ 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => (1 - t) * Real.exp (t * y) / y + Real.exp (t * y) / y ^ 2)
        ((1 - t) * Real.exp (t * y)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t * y) y t := by
      simpa using (hasDerivAt_id t).mul_const y
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (t * y)) (Real.exp (t * y) * y) t := h1.exp
    have h3 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have h4 := ((h3.mul h2).div_const y).add (h2.div_const (y ^ 2))
    refine h4.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t) * Real.exp (t * y)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [zero_mul, Real.exp_zero, one_mul, sub_self, mul_one, zero_div, zero_add, sub_zero]
  field_simp
  ring

lemma G_mono (y₁ y₂ : ℝ) (h : y₁ ≤ y₂) :
    ∫ t in (0:ℝ)..1, (1 - t) * Real.exp (t * y₁) ≤ ∫ t in (0:ℝ)..1, (1 - t) * Real.exp (t * y₂) := by
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  intro t ht
  apply mul_le_mul_of_nonneg_left _ (by linarith [ht.2])
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left h ht.1

/-- Key two-variable inequality: for `s > 0` and `y ≥ -s`,
`s² (e^y - 1 - y) ≥ y² (e^{-s} - 1 + s)`. -/
lemma key_ineq (s y : ℝ) (hs : 0 < s) (hy : -s ≤ y) :
    y ^ 2 * (Real.exp (-s) - 1 + s) ≤ s ^ 2 * (Real.exp y - 1 - y) := by
  by_cases hy0 : y = 0
  · subst hy0; simp
  have hs0 : s ≠ 0 := hs.ne'
  have hG := G_mono (-s) y hy
  rw [G_integral (-s) (by intro h; apply hs0; linarith), G_integral y hy0] at hG
  have hns : -s ≠ 0 := by intro h; apply hs0; linarith
  have hy2 : 0 < y ^ 2 := by positivity
  have hs2 : 0 < (-s) ^ 2 := by positivity
  rw [div_le_div_iff₀ hs2 hy2] at hG
  have e1 : Real.exp (-s) - 1 - -s = Real.exp (-s) - 1 + s := by ring
  rw [e1] at hG
  linarith

/-- Pointwise inequality: for `λ ≥ 0`, `s > 0`, `t ≥ -s`,
`1 + λ t + t² f(λ s)/s² ≤ e^{λ t}`. -/
lemma pointwise_lower (lam s t : ℝ) (hlam : 0 ≤ lam) (hs : 0 < s) (ht : -s ≤ t) :
    1 + lam * t + t ^ 2 * (f (lam * s) / s ^ 2) ≤ Real.exp (lam * t) := by
  rcases hlam.eq_or_lt with h0 | hpos
  · subst h0; simp [f]
  have hk := key_ineq (lam * s) (lam * t) (by positivity)
    (by have := mul_le_mul_of_nonneg_left ht hpos.le; linarith)
  have hf : f (lam * s) = Real.exp (-(lam * s)) - 1 + lam * s := rfl
  rw [hf]
  have hs2 : 0 < s ^ 2 := by positivity
  rw [← sub_nonneg]
  have : Real.exp (lam * t) - (1 + lam * t + t ^ 2 * ((Real.exp (-(lam * s)) - 1 + lam * s) / s ^ 2))
      = (lam ^ 2 * s ^ 2 * (Real.exp (lam * t) - 1 - lam * t)
          - (lam * t) ^ 2 * (Real.exp (-(lam * s)) - 1 + lam * s)) / (lam ^ 2 * s ^ 2) := by
    field_simp
    ring
  rw [this]
  apply div_nonneg _ (by positivity)
  have : (lam * s) ^ 2 * (Real.exp (lam * t) - 1 - lam * t)
      = lam ^ 2 * s ^ 2 * (Real.exp (lam * t) - 1 - lam * t) := by ring
  linarith

/-- The Case-1 real inequality: for `a ≥ 0`, `λ ≥ 0`,
`(1 + a) exp(a (e^{-λ} - 1)) ≤ 1 + a e^{-λ (1 + a)}`. -/
lemma case1_real (a : ℝ) (ha : 0 ≤ a) (lam : ℝ) (hlam : 0 ≤ lam) :
    (1 + a) * Real.exp (a * (Real.exp (-lam) - 1)) ≤ 1 + a * Real.exp (-(lam * (1 + a))) := by
  let φ : ℝ → ℝ := fun x => 1 + a * Real.exp (-(x * (1 + a))) - (1 + a) * Real.exp (a * (Real.exp (-x) - 1))
  have hd : ∀ x, HasDerivAt φ
      (a * (Real.exp (-(x * (1 + a))) * (-(1 + a)))
        - (1 + a) * (Real.exp (a * (Real.exp (-x) - 1)) * (a * (Real.exp (-x) * (-1))))) x := by
    intro x
    have hA : HasDerivAt (fun x : ℝ => -(x * (1 + a))) (-(1 + a)) x := by
      exact (((hasDerivAt_id' (x := x)).mul_const (1 + a)).neg).congr_deriv (by ring)
    have hB : HasDerivAt (fun x : ℝ => Real.exp (-(x * (1 + a))))
        (Real.exp (-(x * (1 + a))) * (-(1 + a))) x := hA.exp
    have hC : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * (-1)) x :=
      (hasDerivAt_neg x).exp
    have hD : HasDerivAt (fun x : ℝ => a * (Real.exp (-x) - 1)) (a * (Real.exp (-x) * (-1))) x :=
      (hC.sub_const 1).const_mul a
    have hE : HasDerivAt (fun x : ℝ => Real.exp (a * (Real.exp (-x) - 1)))
        (Real.exp (a * (Real.exp (-x) - 1)) * (a * (Real.exp (-x) * (-1)))) x := hD.exp
    exact ((hB.const_mul a).const_add 1).sub (hE.const_mul (1 + a))
  have hmono : MonotoneOn φ (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := hx
      rw [(hd x).deriv]
      have key : Real.exp (-(x * (1 + a))) ≤ Real.exp (a * (Real.exp (-x) - 1)) * Real.exp (-x) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [Real.add_one_le_exp (-x)]
      have : a * (Real.exp (-(x * (1 + a))) * (-(1 + a)))
          - (1 + a) * (Real.exp (a * (Real.exp (-x) - 1)) * (a * (Real.exp (-x) * (-1))))
          = a * (1 + a) * (Real.exp (a * (Real.exp (-x) - 1)) * Real.exp (-x)
              - Real.exp (-(x * (1 + a)))) := by ring
      rw [this]
      apply mul_nonneg (by positivity)
      linarith
  have h0 : φ 0 = 0 := by simp [φ]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hlam) hlam
  rw [h0] at this
  simp only [φ] at this
  linarith

/-- Combining: for `m ≥ 0`, `λ ≥ 0`,
`exp(f(λ) m) ≤ exp(λ m) (1 - λ m + κ (m + m²))`, `κ = f(λ(1+m))/(1+m)²`. -/
lemma final_real (m lam : ℝ) (hm : 0 ≤ m) (hlam : 0 ≤ lam) :
    Real.exp (f lam * m) ≤
      Real.exp (lam * m) * (1 - lam * m + (f (lam * (1 + m)) / (1 + m) ^ 2) * (m + m ^ 2)) := by
  have hR := case1_real m hm lam hlam
  have hf1 : f lam = Real.exp (-lam) - 1 + lam := rfl
  have hf2 : f (lam * (1 + m)) = Real.exp (-(lam * (1 + m))) - 1 + lam * (1 + m) := rfl
  have h1m : 0 < 1 + m := by linarith
  have e1 : Real.exp (f lam * m) = Real.exp (lam * m) * Real.exp (m * (Real.exp (-lam) - 1)) := by
    rw [← Real.exp_add, hf1]; congr 1; ring
  have e2 : 1 - lam * m + (f (lam * (1 + m)) / (1 + m) ^ 2) * (m + m ^ 2)
      = (1 + m * Real.exp (-(lam * (1 + m)))) / (1 + m) := by
    rw [hf2]
    field_simp
    ring
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [le_div_iff₀ h1m]
  linarith

/-! ### The inequality (3.7) -/

theorem ineq_3_7_core {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX_L2 : MemLp X 2 P)
    (hX_ge : ∀ᵐ ω ∂P, -1 ≤ X ω) (hX_mean : P[X] = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ENNReal.ofReal (Real.exp (f lam * variance X P)) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂P := by
  set v := variance X P with hv
  have hv0 : 0 ≤ v := variance_nonneg X P
  have hXint : Integrable X P := hX_L2.integrable one_le_two
  have hX2 : Integrable (fun ω => X ω ^ 2) P := hX_L2.integrable_sq
  have hvar : v = ∫ ω, X ω ^ 2 ∂P := by
    rw [hv, variance_eq_integral hX_L2.aemeasurable, hX_mean]
    simp
  set κ := f (lam * (1 + v)) / (1 + v) ^ 2 with hκ
  -- the quadratic minorant, in expanded form
  let g : Ω → ℝ := fun ω => Real.exp (lam * v) *
    ((1 - lam * v + κ * v ^ 2) + (lam - 2 * κ * v) * X ω + κ * X ω ^ 2)
  have hg_int : Integrable g P := by
    apply Integrable.const_mul
    apply Integrable.add
    · apply Integrable.add (integrable_const _) (hXint.const_mul _)
    · exact hX2.const_mul _
  have hg_le : ∀ᵐ ω ∂P, g ω ≤ Real.exp (lam * X ω) := by
    filter_upwards [hX_ge] with ω hω
    have hp := pointwise_lower lam (1 + v) (X ω - v) hlam (by linarith) (by linarith)
    have e : Real.exp (lam * X ω) = Real.exp (lam * v) * Real.exp (lam * (X ω - v)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have : (1 - lam * v + κ * v ^ 2) + (lam - 2 * κ * v) * X ω + κ * X ω ^ 2
        = 1 + lam * (X ω - v) + (X ω - v) ^ 2 * κ := by ring
    rw [this]
    exact hp
  have hg_val : ∫ ω, g ω ∂P = Real.exp (lam * v) * (1 - lam * v + κ * (v + v ^ 2)) := by
    simp only [g]
    rw [integral_const_mul, integral_add, integral_add, integral_const, integral_const_mul,
      integral_const_mul, hX_mean, ← hvar]
    · simp; ring
    · exact integrable_const _
    · exact hXint.const_mul _
    · exact (integrable_const _).add (hXint.const_mul _)
    · exact hX2.const_mul _
  have hreal : Real.exp (f lam * v) ≤ ∫ ω, g ω ∂P := by
    rw [hg_val]; exact final_real v lam hv0 hlam
  -- pass to the lower integral
  have hpos : Integrable (fun ω => max (g ω) 0) P := hg_int.pos_part
  calc ENNReal.ofReal (Real.exp (f lam * v))
      ≤ ENNReal.ofReal (∫ ω, max (g ω) 0 ∂P) := by
        apply ENNReal.ofReal_le_ofReal
        refine hreal.trans (integral_mono hg_int hpos ?_)
        intro ω; exact le_max_left _ _
    _ = ∫⁻ ω, ENNReal.ofReal (max (g ω) 0) ∂P := by
        rw [ofReal_integral_eq_lintegral_ofReal hpos]
        exact Filter.Eventually.of_forall fun ω => le_max_right _ _
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hg_le] with ω hω
        apply ENNReal.ofReal_le_ofReal
        exact max_le hω (Real.exp_pos _).le

end FreedmanTail.Laplace

open FreedmanTail.Laplace


theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX_L2 : MemLp X 2 P)
    (hX_ge : ∀ᵐ ω ∂P, -1 ≤ X ω) (hX_mean : P[X] = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ENNReal.ofReal (Real.exp (f lam * variance X P)) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂P := by
  exact ineq_3_7_core P X hX_L2 hX_ge hX_mean lam hlam
