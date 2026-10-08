-- Prove2me | solution 1 for FreedmanTail.Laplace.proposition_3_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:46:38.719853+00:00
-- url     : https://prove2.me/submissions/6560b299-09fb-44a2-8659-612f8beb22e7

import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

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


/-! ### Conditional version of (3.7) -/

section Conditional

noncomputable def kap (lam v : ℝ) : ℝ := f (lam * (1 + v)) / (1 + v) ^ 2
noncomputable def coefA (lam v : ℝ) : ℝ := Real.exp (lam * v) * (1 - lam * v + kap lam v * v ^ 2)
noncomputable def coefB (lam v : ℝ) : ℝ := Real.exp (lam * v) * (lam - 2 * kap lam v * v)
noncomputable def coefC (lam v : ℝ) : ℝ := Real.exp (lam * v) * kap lam v

lemma measurable_kap (lam : ℝ) : Measurable (kap lam) := by
  unfold kap f; fun_prop

lemma measurable_coefA (lam : ℝ) : Measurable (coefA lam) := by
  unfold coefA; have := measurable_kap lam; fun_prop

lemma measurable_coefB (lam : ℝ) : Measurable (coefB lam) := by
  unfold coefB; have := measurable_kap lam; fun_prop

lemma measurable_coefC (lam : ℝ) : Measurable (coefC lam) := by
  unfold coefC; have := measurable_kap lam; fun_prop

lemma continuousOn_kap (lam : ℝ) : ContinuousOn (kap lam) (Set.Icc 0 1) := by
  unfold kap f
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro v hv
  have := hv.1
  positivity

lemma continuousOn_coefA (lam : ℝ) : ContinuousOn (coefA lam) (Set.Icc 0 1) := by
  unfold coefA
  have := continuousOn_kap lam
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.add (by fun_prop)
  exact this.mul (by fun_prop)

lemma continuousOn_coefB (lam : ℝ) : ContinuousOn (coefB lam) (Set.Icc 0 1) := by
  unfold coefB
  have := continuousOn_kap lam
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.sub (by fun_prop)
  exact (continuousOn_const.mul this).mul continuousOn_id

lemma continuousOn_coefC (lam : ℝ) : ContinuousOn (coefC lam) (Set.Icc 0 1) := by
  unfold coefC
  exact ContinuousOn.mul (by fun_prop) (continuousOn_kap lam)

lemma bound_of_continuousOn {φ : ℝ → ℝ} (h : ContinuousOn φ (Set.Icc 0 1)) :
    ∃ C, ∀ v ∈ Set.Icc (0:ℝ) 1, |φ v| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn h
  exact ⟨C, fun v hv => by simpa [Real.norm_eq_abs] using hC v hv⟩

/-- Conditional form of (3.7) for a bounded increment: if `|Y| ≤ 1` a.s. and `E[Y | G] = 0`,
then `exp(f(λ) Var[Y | G]) ≤ E[exp(λ Y) | G]` a.s. -/
theorem cond_ineq_3_7 {Ω : Type*} (G : MeasurableSpace Ω) {m0 : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] (hG : G ≤ m0) (Y : Ω → ℝ)
    (hY_meas : AEStronglyMeasurable Y P)
    (hY_bdd : ∀ᵐ ω ∂P, |Y ω| ≤ 1)
    (hY_mart : P[Y | G] =ᵐ[P] 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (fun ω => Real.exp (f lam * condVar G Y P ω)) ≤ᵐ[P] P[fun ω => Real.exp (lam * Y ω) | G] := by
  have hVmeas : StronglyMeasurable[G] (condVar G Y P) := stronglyMeasurable_condVar
  have hVmeas' : Measurable (condVar G Y P) := (hVmeas.mono hG).measurable
  have hY_L2 : MemLp Y 2 P := by
    apply MemLp.of_bound hY_meas 1
    filter_upwards [hY_bdd] with ω hω
    simpa [Real.norm_eq_abs] using hω
  have hY_int : Integrable Y P := hY_L2.integrable one_le_two
  have hY2_int : Integrable (Y ^ 2) P := hY_L2.integrable_sq
  have hY2_bdd : ∀ᵐ ω ∂P, (Y ^ 2) ω ≤ 1 := by
    filter_upwards [hY_bdd] with ω hω
    simp only [Pi.pow_apply]
    nlinarith [abs_le.mp hω]
  have hV_eq : condVar G Y P =ᵐ[P] P[Y ^ 2 | G] := by
    filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hG hY_L2, hY_mart] with ω h1 h2
    rw [h1]
    simp only [Pi.sub_apply, Pi.pow_apply, h2, Pi.zero_apply]
    ring
  have hV_nonneg : ∀ᵐ ω ∂P, 0 ≤ condVar G Y P ω := by
    filter_upwards [hV_eq, condExp_nonneg (m := G) (μ := P) (f := Y ^ 2)
      (Filter.Eventually.of_forall fun ω => by simp only [Pi.pow_apply]; positivity)] with ω h1 h2
    rw [h1]; exact h2
  have hV_le : ∀ᵐ ω ∂P, condVar G Y P ω ≤ 1 := by
    have h := condExp_mono (m := G) hY2_int (integrable_const (1:ℝ)) hY2_bdd
    rw [condExp_const hG] at h
    filter_upwards [hV_eq, h] with ω h1 h2
    rw [h1]; exact h2
  set V := condVar G Y P with hVdef
  -- bounds for the coefficient functions
  obtain ⟨CA, hCA⟩ := bound_of_continuousOn (continuousOn_coefA lam)
  obtain ⟨CB, hCB⟩ := bound_of_continuousOn (continuousOn_coefB lam)
  obtain ⟨CC, hCC⟩ := bound_of_continuousOn (continuousOn_coefC lam)
  have hVIcc : ∀ᵐ ω ∂P, V ω ∈ Set.Icc (0:ℝ) 1 := by
    filter_upwards [hV_nonneg, hV_le] with ω h1 h2
    exact ⟨h1, h2⟩
  -- the three pieces
  let gA : Ω → ℝ := fun ω => coefA lam (V ω)
  let gB : Ω → ℝ := fun ω => coefB lam (V ω)
  let gC : Ω → ℝ := fun ω => coefC lam (V ω)
  have hgA_meas : StronglyMeasurable[G] gA :=
    ((measurable_coefA lam).comp hVmeas.measurable).stronglyMeasurable
  have hgB_meas : StronglyMeasurable[G] gB :=
    ((measurable_coefB lam).comp hVmeas.measurable).stronglyMeasurable
  have hgC_meas : StronglyMeasurable[G] gC :=
    ((measurable_coefC lam).comp hVmeas.measurable).stronglyMeasurable
  have hgA_int : Integrable gA P := by
    apply Integrable.of_bound (C := CA) (hgA_meas.mono hG).aestronglyMeasurable
    filter_upwards [hVIcc] with ω hω
    simpa [Real.norm_eq_abs] using hCA _ hω
  have hgBY_int : Integrable (gB * Y) P := by
    apply Integrable.of_bound (C := |CB|) ((hgB_meas.mono hG).aestronglyMeasurable.mul hY_meas)
    filter_upwards [hVIcc, hY_bdd] with ω hω hY
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    calc |gB ω| * |Y ω| ≤ CB * 1 := by
          apply mul_le_mul (hCB _ hω) hY (abs_nonneg _) ((abs_nonneg _).trans (hCB _ hω))
      _ ≤ |CB| := by rw [mul_one]; exact le_abs_self _
  have hgCY_int : Integrable (gC * Y ^ 2) P := by
    apply Integrable.of_bound (C := |CC|)
      ((hgC_meas.mono hG).aestronglyMeasurable.mul (hY_meas.pow 2))
    filter_upwards [hVIcc, hY2_bdd] with ω hω hY
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    have h0 : 0 ≤ (Y ^ 2) ω := by simp only [Pi.pow_apply]; positivity
    calc |gC ω| * |(Y ^ 2) ω| ≤ CC * 1 := by
          rw [abs_of_nonneg h0]
          apply mul_le_mul (hCC _ hω) hY h0 ((abs_nonneg _).trans (hCC _ hω))
      _ ≤ |CC| := by rw [mul_one]; exact le_abs_self _
  let g : Ω → ℝ := gA + gB * Y + gC * Y ^ 2
  have hg_int : Integrable g P := (hgA_int.add hgBY_int).add hgCY_int
  have hexp_int : Integrable (fun ω => Real.exp (lam * Y ω)) P := by
    apply Integrable.of_bound (C := Real.exp lam)
    · exact (Real.continuous_exp.comp_aestronglyMeasurable (hY_meas.const_mul lam))
    · filter_upwards [hY_bdd] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc lam * Y ω ≤ lam * 1 := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hω) hlam
        _ = lam := mul_one lam
  -- pointwise minorant
  have hg_le : g ≤ᵐ[P] fun ω => Real.exp (lam * Y ω) := by
    filter_upwards [hV_nonneg, hY_bdd] with ω hV hY
    have hY1 : -1 ≤ Y ω := (abs_le.mp hY).1
    have hp := pointwise_lower lam (1 + V ω) (Y ω - V ω) hlam (by linarith) (by linarith)
    have e : Real.exp (lam * Y ω) = Real.exp (lam * V ω) * Real.exp (lam * (Y ω - V ω)) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [g, gA, gB, gC, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, coefA, coefB, coefC, kap]
    rw [e]
    have : Real.exp (lam * V ω) * (1 - lam * V ω + f (lam * (1 + V ω)) / (1 + V ω) ^ 2 * V ω ^ 2)
        + Real.exp (lam * V ω) * (lam - 2 * (f (lam * (1 + V ω)) / (1 + V ω) ^ 2) * V ω) * Y ω
        + Real.exp (lam * V ω) * (f (lam * (1 + V ω)) / (1 + V ω) ^ 2) * Y ω ^ 2
        = Real.exp (lam * V ω) *
          (1 + lam * (Y ω - V ω) + (Y ω - V ω) ^ 2 * (f (lam * (1 + V ω)) / (1 + V ω) ^ 2)) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
  -- conditional expectation of the minorant
  have hcond_g : P[g | G] =ᵐ[P] gA + gC * V := by
    have h1 := condExp_add (m := G) (hgA_int.add hgBY_int) hgCY_int
    have h2 := condExp_add (m := G) hgA_int hgBY_int
    have h3 : P[gA | G] = gA := condExp_of_stronglyMeasurable hG hgA_meas hgA_int
    have h4 := condExp_mul_of_stronglyMeasurable_left (μ := P) hgB_meas hgBY_int hY_int
    have h5 := condExp_mul_of_stronglyMeasurable_left (μ := P) hgC_meas hgCY_int hY2_int
    filter_upwards [h1, h2, h4, h5, hY_mart, hV_eq] with ω e1 e2 e4 e5 e6 e7
    simp only [g] at e1 ⊢
    rw [e1, Pi.add_apply, e2, Pi.add_apply, h3, e4, e5]
    simp only [Pi.add_apply, Pi.mul_apply, e6, Pi.zero_apply, mul_zero, add_zero]
    rw [e7]
  have hfinal : ∀ᵐ ω ∂P, Real.exp (f lam * V ω) ≤ (gA + gC * V) ω := by
    filter_upwards [hV_nonneg] with ω hV
    have := final_real (V ω) lam hV hlam
    simp only [Pi.add_apply, Pi.mul_apply, gA, gC, coefA, coefC, kap]
    calc Real.exp (f lam * V ω)
        ≤ Real.exp (lam * V ω) * (1 - lam * V ω + f (lam * (1 + V ω)) / (1 + V ω) ^ 2 * (V ω + V ω ^ 2)) := this
      _ = _ := by ring
  have hmono := condExp_mono (m := G) hg_int hexp_int hg_le
  filter_upwards [hfinal, hcond_g, hmono] with ω h1 h2 h3
  rw [← h2] at h1
  exact h1.trans h3

end Conditional


/-! ### The exponential submartingale and Proposition (3.6) -/

section Submartingale

open FreedmanTail.Bernstein

lemma f_nonneg (lam : ℝ) (hlam : 0 ≤ lam) : 0 ≤ f lam := by
  unfold f; linarith [Real.add_one_le_exp (-lam)]

lemma S_succ {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    S X (k + 1) ω = S X k ω + X (k + 1) ω := by
  unfold S; rw [Finset.sum_Icc_succ_top (by omega)]

lemma T_succ {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (P : Measure Ω) (k : ℕ) (ω : Ω) :
    T ℱ X P (k + 1) ω = T ℱ X P k ω + V ℱ X P (k + 1) ω := by
  unfold T; rw [Finset.sum_Icc_succ_top (by omega)]

/-- The exponential process `R_λ(T_n, S_n)` is a submartingale. -/
theorem R_submartingale {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Submartingale (fun n ω => R lam (T ℱ X P n ω) (S X n ω)) ℱ P := by
  set M : ℕ → Ω → ℝ := fun n ω => R lam (T ℱ X P n ω) (S X n ω) with hM
  have hf0 := f_nonneg lam hlam
  -- a.e. bounds on all increments and conditional variances
  have hV : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, 0 ≤ V ℱ X P n ω ∧ V ℱ X P n ω ≤ 1 := by
    intro n hn
    have hYm : AEStronglyMeasurable (X n) P := ((hX_meas n hn).mono (ℱ.le n)).aestronglyMeasurable
    have hL2 : MemLp (X n) 2 P := by
      apply MemLp.of_bound hYm 1
      filter_upwards [hX_bdd n hn] with ω hω
      simpa [Real.norm_eq_abs] using hω
    have h2int : Integrable (X n ^ 2) P := hL2.integrable_sq
    have h2bdd : ∀ᵐ ω ∂P, (X n ^ 2) ω ≤ 1 := by
      filter_upwards [hX_bdd n hn] with ω hω
      simp only [Pi.pow_apply]
      nlinarith [abs_le.mp hω]
    have hV_eq : V ℱ X P n =ᵐ[P] P[X n ^ 2 | ℱ (n - 1)] := by
      filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le (n - 1)) hL2, hX_mart n hn]
        with ω h1 h2
      unfold V
      rw [h1]
      simp only [Pi.sub_apply, Pi.pow_apply, h2, Pi.zero_apply]
      ring
    have hmono := condExp_mono (m := ℱ (n - 1)) h2int (integrable_const (1:ℝ)) h2bdd
    rw [condExp_const (ℱ.le (n - 1))] at hmono
    filter_upwards [hV_eq, hmono, condExp_nonneg (m := ℱ (n - 1)) (μ := P) (f := X n ^ 2)
      (Filter.Eventually.of_forall fun ω => by simp only [Pi.pow_apply]; positivity)]
      with ω h1 h2 h3
    rw [h1]
    exact ⟨h3, h2⟩
  have hall : ∀ᵐ ω ∂P, ∀ i, 1 ≤ i → (|X i ω| ≤ 1 ∧ 0 ≤ V ℱ X P i ω ∧ V ℱ X P i ω ≤ 1) := by
    rw [ae_all_iff]
    intro i
    by_cases hi : 1 ≤ i
    · filter_upwards [hX_bdd i hi, hV i hi] with ω h1 h2
      exact fun _ => ⟨h1, h2⟩
    · exact Filter.Eventually.of_forall fun ω h => absurd h hi
  -- adaptedness
  have hS : ∀ n, StronglyMeasurable[ℱ n] (S X n) := by
    intro n
    unfold S
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    have := Finset.mem_Icc.mp hi
    exact (hX_meas i this.1).mono (ℱ.mono this.2)
  have hT : ∀ n, StronglyMeasurable[ℱ n] (T ℱ X P n) := by
    intro n
    unfold T
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    have := Finset.mem_Icc.mp hi
    exact (stronglyMeasurable_condVar).mono (ℱ.mono (by omega))
  have hadp : StronglyAdapted ℱ M := by
    intro n
    show StronglyMeasurable[ℱ n] (fun ω => Real.exp (lam * S X n ω - f lam * T ℱ X P n ω))
    exact Real.continuous_exp.comp_stronglyMeasurable (((hS n).const_mul lam).sub ((hT n).const_mul (f lam)))
  -- integrability
  have hint : ∀ n, Integrable (M n) P := by
    intro n
    apply Integrable.of_bound (C := Real.exp (lam * n)) ((hadp n).mono (ℱ.le n)).aestronglyMeasurable
    filter_upwards [hall] with ω hω
    simp only [M, R]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hSle : S X n ω ≤ n := by
      unfold S
      calc ∑ i ∈ Finset.Icc 1 n, X i ω ≤ ∑ i ∈ Finset.Icc 1 n, (1:ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact (le_abs_self _).trans (hω i (Finset.mem_Icc.mp hi).1).1
        _ = n := by simp
    have hT0 : 0 ≤ T ℱ X P n ω := by
      unfold T
      apply Finset.sum_nonneg
      intro i hi
      exact (hω i (Finset.mem_Icc.mp hi).1).2.1
    nlinarith
  -- one-step inequality
  have hstep : ∀ n, M n ≤ᵐ[P] P[M (n + 1) | ℱ n] := by
    intro n
    have hn1 : 1 ≤ n + 1 := by omega
    have hVn : V ℱ X P (n + 1) = condVar (ℱ n) (X (n + 1)) P := by
      unfold V; simp
    set E1 : Ω → ℝ := fun ω => Real.exp (-(f lam * V ℱ X P (n + 1) ω)) with hE1
    set E2 : Ω → ℝ := fun ω => Real.exp (lam * X (n + 1) ω) with hE2
    have hsplit : M (n + 1) = (M n * E1) * E2 := by
      funext ω
      simp only [M, R, E1, E2, Pi.mul_apply, S_succ, T_succ]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    have hE1_meas : StronglyMeasurable[ℱ n] E1 := by
      rw [hE1, hVn]
      exact Real.continuous_exp.comp_stronglyMeasurable
        ((stronglyMeasurable_condVar.const_mul (f lam)).neg)
    have hE2_int : Integrable E2 P := by
      apply Integrable.of_bound (C := Real.exp lam)
      · exact Real.continuous_exp.comp_aestronglyMeasurable
          (((hX_meas (n + 1) hn1).mono (ℱ.le _)).aestronglyMeasurable.const_mul lam)
      · filter_upwards [hX_bdd (n + 1) hn1] with ω hω
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        calc lam * X (n + 1) ω ≤ lam * 1 :=
              mul_le_mul_of_nonneg_left ((le_abs_self _).trans hω) hlam
          _ = lam := mul_one lam
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ := P) ((hadp n).mul hE1_meas)
      (hsplit ▸ hint (n + 1)) hE2_int
    have hmart' : P[X (n + 1) | ℱ n] =ᵐ[P] 0 := by
      have := hX_mart (n + 1) hn1
      simpa using this
    have hc37 := cond_ineq_3_7 (ℱ n) (ℱ.le n) (X (n + 1))
      ((hX_meas (n + 1) hn1).mono (ℱ.le _)).aestronglyMeasurable (hX_bdd (n + 1) hn1) hmart' lam hlam
    rw [hsplit]
    filter_upwards [hpull, hc37] with ω h1 h2
    rw [h1]
    simp only [Pi.mul_apply]
    have hpos : 0 ≤ M n ω * E1 ω := by
      simp only [M, R, E1]; positivity
    calc M n ω = M n ω * E1 ω * Real.exp (f lam * condVar (ℱ n) (X (n + 1)) P ω) := by
          simp only [E1, hVn]
          rw [mul_assoc, ← Real.exp_add]
          simp
      _ ≤ M n ω * E1 ω * P[E2 | ℱ n] ω := mul_le_mul_of_nonneg_left h2 hpos
  exact submartingale_nat hadp hint hstep

theorem proposition_3_6_core {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (σ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) (hσ_bdd : ∃ N : ℕ, ∀ ω, σ ω ≤ N)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    1 ≤ ∫ ω, R lam (T ℱ X P ((σ ω).untopD 0) ω) (S X ((σ ω).untopD 0) ω) ∂P := by
  obtain ⟨N, hN⟩ := hσ_bdd
  have hsub := R_submartingale P ℱ X hX_meas hX_bdd hX_mart lam hlam
  set M : ℕ → Ω → ℝ := fun n ω => R lam (T ℱ X P n ω) (S X n ω) with hM
  have h0 : IsStoppingTime ℱ (fun _ => ((0 : ℕ) : WithTop ℕ)) := isStoppingTime_const ℱ 0
  have hle : (fun _ => ((0 : ℕ) : WithTop ℕ)) ≤ σ := fun ω => by simp
  have key := hsub.expected_stoppedValue_mono h0 hσ hle hN
  have hM0 : ∫ ω, stoppedValue M (fun _ => ((0 : ℕ) : WithTop ℕ)) ω ∂P = 1 := by
    change ∫ ω, M 0 ω ∂P = 1
    simp [M, R, S, T]
  have hEq : (fun ω => stoppedValue M σ ω) =
      fun ω => R lam (T ℱ X P ((σ ω).untopD 0) ω) (S X ((σ ω).untopD 0) ω) := by
    funext ω
    have hne : σ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hN ω)
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
    simp only [stoppedValue, M, ← hk]
    rfl
  rw [hM0] at key
  rw [← hEq]
  exact key

end Submartingale

end FreedmanTail.Laplace

open FreedmanTail.Laplace


theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (σ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) (hσ_bdd : ∃ N : ℕ, ∀ ω, σ ω ≤ N)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    1 ≤ ∫ ω, R lam (FreedmanTail.Bernstein.T ℱ X P ((σ ω).untopD 0) ω) (FreedmanTail.Bernstein.S X ((σ ω).untopD 0) ω) ∂P := by
  exact proposition_3_6_core P ℱ X hX_meas hX_bdd hX_mart σ hσ hσ_bdd lam hlam
