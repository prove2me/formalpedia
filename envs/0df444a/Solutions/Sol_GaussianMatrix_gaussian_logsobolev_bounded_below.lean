-- Prove2me | solution 1 for GaussianMatrix.gaussian_logsobolev_bounded_below
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:11:28.031146+00:00
-- url     : https://prove2.me/submissions/655bc739-b82f-4cf8-a991-8fff4f031e7b

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_ou_entropy_hasDerivAt
import Theorems.Thm_GaussianMatrix_ou_semigroup_invariant
import Theorems.Thm_GaussianMatrix_ou_semigroup_commutation

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

open Filter Topology Set

/-- The one-dimensional Ornstein–Uhlenbeck semigroup (Mehler formula). -/
noncomputable def ouSG (t : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, h (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y) ∂(gaussianReal 0 1)

/-- `|s log s| ≤ s² + 1` for `s ≥ 0`. -/
lemma abs_mul_log_le_sq_add_one' (s : ℝ) (hs : 0 ≤ s) : |s * Real.log s| ≤ s ^ 2 + 1 := by
  rcases hs.eq_or_lt with h | hs'
  · subst h; simp
  rcases le_or_gt s 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt s hs' h1
    rw [mul_comm]; nlinarith [sq_nonneg s]
  · have hl : 0 ≤ Real.log s := Real.log_nonneg h1.le
    have hl2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs'
    rw [abs_of_nonneg (mul_nonneg hs hl)]
    nlinarith

/-- Cauchy–Schwarz in the form `(∫ a)² ≤ (∫ a²/b) (∫ b)` for `b ≥ δ > 0`. -/
lemma sq_integral_le_integral_div_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (a b : α → ℝ) (δ : ℝ) (hδ : 0 < δ) (hb : ∀ x, δ ≤ b x)
    (ha : Integrable a μ) (hbi : Integrable b μ) (hab : Integrable (fun x => a x ^ 2 / b x) μ) :
    (∫ x, a x ∂μ) ^ 2 ≤ (∫ x, a x ^ 2 / b x ∂μ) * (∫ x, b x ∂μ) := by
  set A := ∫ x, a x ∂μ
  set B := ∫ x, b x ∂μ
  set Q := ∫ x, a x ^ 2 / b x ∂μ
  have hB : δ ≤ B := by
    have := integral_mono (integrable_const δ) hbi hb
    simpa using this
  have hBpos : 0 < B := lt_of_lt_of_le hδ hB
  set l := A / B
  have hpt : ∀ x, (a x - l * b x) ^ 2 / b x = a x ^ 2 / b x - 2 * l * a x + l ^ 2 * b x := by
    intro x
    have : b x ≠ 0 := (lt_of_lt_of_le hδ (hb x)).ne'
    field_simp
    ring
  have hnonneg : 0 ≤ ∫ x, (a x - l * b x) ^ 2 / b x ∂μ := by
    refine integral_nonneg (fun x => div_nonneg (sq_nonneg _) (hδ.le.trans (hb x)))
  have hcalc : ∫ x, (a x - l * b x) ^ 2 / b x ∂μ = Q - 2 * l * A + l ^ 2 * B := by
    simp_rw [hpt]
    have h1 : Integrable (fun x => a x ^ 2 / b x - 2 * l * a x) μ := hab.sub (ha.const_mul _)
    have h2 : Integrable (fun x => l ^ 2 * b x) μ := hbi.const_mul _
    have h3 : Integrable (fun x => 2 * l * a x) μ := ha.const_mul _
    rw [integral_add h1 h2, integral_sub hab h3, integral_const_mul, integral_const_mul]
  rw [hcalc] at hnonneg
  have : Q - 2 * l * A + l ^ 2 * B = Q - A ^ 2 / B := by
    simp only [l]; field_simp; ring
  rw [this, sub_nonneg, div_le_iff₀ hBpos] at hnonneg
  exact hnonneg

end GaussianMatrix

open GaussianMatrix Filter Topology Set

theorem solution (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (δ C : ℝ)
    (hδ : 0 < δ) (hlow : ∀ x, δ ≤ f x) (hup : ∀ x, f x ≤ C) (hdf : ∀ x, |deriv f x| ≤ C) :
    ∫ x, f x * Real.log (f x) ∂(gaussianReal 0 1)
      - (∫ x, f x ∂(gaussianReal 0 1)) * Real.log (∫ x, f x ∂(gaussianReal 0 1))
      ≤ (1 / 2) * ∫ x, deriv f x ^ 2 / f x ∂(gaussianReal 0 1) := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hC : δ ≤ C := (hlow 0).trans (hup 0)
  have hC0 : 0 < C := lt_of_lt_of_le hδ hC
  have hfabs : ∀ x, |f x| ≤ C := fun x => by
    rw [abs_of_pos (lt_of_lt_of_le hδ (hlow x))]; exact hup x
  -- integrability of bounded continuous functions composed with affine maps
  have hint_aff : ∀ (h : ℝ → ℝ), Measurable h → (∀ z, |h z| ≤ C ^ 2 / δ + C) →
      ∀ a b : ℝ, Integrable (fun y => h (a + b * y)) (gaussianReal 0 1) := by
    intro h hm hb a b
    refine Integrable.mono' (integrable_const (C ^ 2 / δ + C))
      (hm.comp (by fun_prop)).aestronglyMeasurable (Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs]; exact hb _
  have hδC : 0 ≤ C ^ 2 / δ := by positivity
  have hf_int : ∀ a b : ℝ, Integrable (fun y => f (a + b * y)) (gaussianReal 0 1) :=
    hint_aff f hfc.measurable (fun z => by linarith [hfabs z])
  -- basic bounds on the semigroup
  have hP_low : ∀ t x, δ ≤ ouSG t f x := by
    intro t x
    have := integral_mono (integrable_const δ)
      (hf_int (Real.exp (-t) * x) (Real.sqrt (1 - Real.exp (-(2 * t))))) (fun y => hlow _)
    simpa [ouSG] using this
  have hP_up : ∀ t x, ouSG t f x ≤ C := by
    intro t x
    have := integral_mono (hf_int (Real.exp (-t) * x) (Real.sqrt (1 - Real.exp (-(2 * t)))))
      (integrable_const C) (fun y => hup _)
    simpa [ouSG] using this
  have hP_pos : ∀ t x, 0 < ouSG t f x := fun t x => lt_of_lt_of_le hδ (hP_low t x)
  have hP0 : ∀ x, ouSG 0 f x = f x := by intro x; simp [ouSG]
  -- differentiability (hence continuity, measurability) in `x`
  have hP_hasDeriv : ∀ t x, HasDerivAt (ouSG t f) (Real.exp (-t) * ouSG t (deriv f) x) x :=
    fun t x => ou_semigroup_commutation f hf C hdf t x
  have hP_cont : ∀ t, Continuous (ouSG t f) := fun t =>
    continuous_iff_continuousAt.2 (fun x => (hP_hasDeriv t x).continuousAt)
  -- continuity in `t`
  have hP_cont_t : ∀ x, Continuous (fun t => ouSG t f x) := by
    intro x
    refine continuous_of_dominated (bound := fun _ => C) (fun t => ?_)
      (fun t => Eventually.of_forall (fun y => ?_)) (integrable_const C)
      (Eventually.of_forall (fun y => ?_))
    · exact (hfc.comp (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hfabs _
    · exact hfc.comp (by fun_prop)
  -- the entropy functional along the semigroup
  set H : ℝ → ℝ := fun t => ∫ x, ouSG t f x * Real.log (ouSG t f x) ∂(gaussianReal 0 1)
    with hHdef
  have hΦbound : ∀ t x, |ouSG t f x * Real.log (ouSG t f x)| ≤ C ^ 2 + 1 := by
    intro t x
    refine (abs_mul_log_le_sq_add_one' _ (hP_pos t x).le).trans ?_
    have := pow_le_pow_left₀ (hP_pos t x).le (hP_up t x) 2
    linarith
  have hH_cont : Continuous H := by
    refine continuous_of_dominated (bound := fun _ => C ^ 2 + 1) (fun t => ?_)
      (fun t => Eventually.of_forall (fun x => ?_)) (integrable_const _)
      (Eventually.of_forall (fun x => ?_))
    · exact ((hP_cont t).measurable.mul (hP_cont t).measurable.log).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hΦbound t x
    · exact Real.continuous_mul_log.comp (hP_cont_t x)
  -- Fisher information and its decay
  set J := ∫ x, deriv f x ^ 2 / f x ∂(gaussianReal 0 1) with hJdef
  set I : ℝ → ℝ := fun t =>
    ∫ x, deriv (ouSG t f) x ^ 2 / ouSG t f x ∂(gaussianReal 0 1) with hIdef
  have hH_deriv : ∀ t, 0 < t → HasDerivAt H (-I t) t := fun t ht =>
    ou_entropy_hasDerivAt f hf δ C hδ hlow hup hdf t ht
  set q : ℝ → ℝ := fun z => deriv f z ^ 2 / f z with hqdef
  have hq_meas : Measurable q := ((measurable_deriv f).pow_const 2).div hfc.measurable
  have hq_bound : ∀ z, |q z| ≤ C ^ 2 / δ + C := by
    intro z
    have hfz := lt_of_lt_of_le hδ (hlow z)
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hfz.le)]
    have h1 : deriv f z ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdf z) 2
    have h2 : deriv f z ^ 2 / f z ≤ C ^ 2 / δ := by
      rw [div_le_div_iff₀ hfz hδ]
      nlinarith [hlow z, sq_nonneg (deriv f z)]
    linarith
  have hq_int : Integrable q (gaussianReal 0 1) := by
    simpa using hint_aff q hq_meas hq_bound 0 1
  have hI_le : ∀ t, 0 ≤ t → I t ≤ Real.exp (-(2 * t)) * J := by
    intro t ht
    have hinv : ∫ x, ouSG t q x ∂(gaussianReal 0 1) = J :=
      ou_semigroup_invariant q hq_int t ht
    -- pointwise Cauchy–Schwarz
    have hpt : ∀ x, deriv (ouSG t f) x ^ 2 / ouSG t f x
        ≤ Real.exp (-(2 * t)) * ouSG t q x := by
      intro x
      rw [(hP_hasDeriv t x).deriv]
      have hCS := sq_integral_le_integral_div_mul (gaussianReal 0 1)
        (fun y => deriv f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y))
        (fun y => f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)) δ hδ
        (fun y => hlow _)
        (hint_aff (deriv f) (measurable_deriv f) (fun z => by
          linarith [hdf z, show C ≤ C ^ 2 / δ + C by linarith]) _ _)
        (hf_int _ _) (hint_aff q hq_meas hq_bound _ _)
      have hP := hP_pos t x
      rw [div_le_iff₀ hP, mul_pow, ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * -t = -(2 * t) := by push_cast; ring
      rw [e, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact hCS
    have hmeas_q : Integrable (ouSG t q) (gaussianReal 0 1) := by
      refine Integrable.mono' (integrable_const (C ^ 2 / δ + C)) ?_
        (Eventually.of_forall (fun x => ?_))
      · refine (StronglyMeasurable.integral_prod_right'
          (f := fun p : ℝ × ℝ => q (Real.exp (-t) * p.1
            + Real.sqrt (1 - Real.exp (-(2 * t))) * p.2)) ?_).aestronglyMeasurable
        exact (hq_meas.comp (by fun_prop)).stronglyMeasurable
      · rw [Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        have := integral_mono (hint_aff q hq_meas hq_bound (Real.exp (-t) * x)
          (Real.sqrt (1 - Real.exp (-(2 * t))))).abs
          (integrable_const (C ^ 2 / δ + C)) (fun y => hq_bound _)
        simpa using this
    calc I t ≤ ∫ x, Real.exp (-(2 * t)) * ouSG t q x ∂(gaussianReal 0 1) := by
          refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_))
            (hmeas_q.const_mul _) (Eventually.of_forall hpt)
          exact div_nonneg (sq_nonneg _) (hP_pos t x).le
      _ = Real.exp (-(2 * t)) * J := by rw [integral_const_mul, hinv]
  -- monotonicity of `Ψ(t) = H(t) - e^{-2t} J / 2` on `[0, ∞)`
  set Ψ : ℝ → ℝ := fun t => H t - (1 / 2) * Real.exp (-(2 * t)) * J with hΨdef
  have hΨ_mono : MonotoneOn Ψ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => -I t + Real.exp (-(2 * t)) * J)
      (convex_Ici 0) (by fun_prop) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Ici] at ht
      have h1 := hH_deriv t ht
      have h2 : HasDerivAt (fun t : ℝ => (1 / 2) * Real.exp (-(2 * t)) * J)
          (-(Real.exp (-(2 * t)) * J)) t := by
        have := (((hasDerivAt_id t).const_mul 2).neg.exp.const_mul (1 / 2)).mul_const J
        refine this.congr_deriv ?_
        simp only [Pi.neg_apply, id]; ring
      exact (h1.sub h2).hasDerivWithinAt.congr_deriv (by ring)
    · rw [interior_Ici] at ht
      have := hI_le t (le_of_lt ht)
      linarith
  -- behaviour at infinity
  set m := ∫ x, f x ∂(gaussianReal 0 1) with hmdef
  have hP_lim : ∀ x, Tendsto (fun t => ouSG t f x) atTop (𝓝 m) := by
    intro x
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      (Eventually.of_forall (fun t => (hfc.comp (by fun_prop)).aestronglyMeasurable))
      (Eventually.of_forall (fun t => Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]; exact hfabs _))) (integrable_const C)
      (Eventually.of_forall (fun y => ?_))
    have h1 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have h2 : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    have h3 : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-(2 * t)))) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h2).sqrt
      simpa using this
    have h4 : Tendsto (fun t : ℝ => Real.exp (-t) * x
        + Real.sqrt (1 - Real.exp (-(2 * t))) * y) atTop (𝓝 y) := by
      have := (h1.mul_const x).add (h3.mul_const y)
      simpa using this
    exact (hfc.tendsto y).comp h4
  have hH_lim : Tendsto H atTop (𝓝 (m * Real.log m)) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1)
      (F := fun t x => ouSG t f x * Real.log (ouSG t f x)) (f := fun _ => m * Real.log m)
      (l := atTop) (fun _ => C ^ 2 + 1)
      (Eventually.of_forall (fun t =>
        ((hP_cont t).measurable.mul (hP_cont t).measurable.log).aestronglyMeasurable))
      (Eventually.of_forall (fun t => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]; exact hΦbound t x))) (integrable_const _)
      (Eventually.of_forall (fun x => (Real.continuous_mul_log.tendsto _).comp (hP_lim x)))
    simpa using this
  have hΨ_lim : Tendsto Ψ atTop (𝓝 (m * Real.log m)) := by
    have h2 : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    have := hH_lim.sub ((h2.const_mul (1 / 2)).mul_const J)
    simpa [Ψ, mul_assoc] using this
  have hΨ0 : Ψ 0 ≤ m * Real.log m := by
    refine ge_of_tendsto hΨ_lim ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hΨ_mono (self_mem_Ici) ht ht
  have hH0 : H 0 = ∫ x, f x * Real.log (f x) ∂(gaussianReal 0 1) := by
    simp only [H, hP0]
  have : Ψ 0 = ∫ x, f x * Real.log (f x) ∂(gaussianReal 0 1) - (1 / 2) * J := by
    simp only [Ψ, hH0]; simp
  rw [this] at hΨ0
  linarith
