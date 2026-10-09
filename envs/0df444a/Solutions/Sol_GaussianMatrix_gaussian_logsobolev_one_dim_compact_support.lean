-- Prove2me | solution 1 for GaussianMatrix.gaussian_logsobolev_one_dim_compact_support
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:15:42.509857+00:00
-- url     : https://prove2.me/submissions/84e67c72-6d2a-4cf1-8add-fa97b0f2422d

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_gaussian_logsobolev_bounded_below

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

open Filter Topology

/-- `|s log s| ≤ s² + 1` for `s ≥ 0`. -/
lemma abs_mul_log_le_sq_add_one (s : ℝ) (hs : 0 ≤ s) : |s * Real.log s| ≤ s ^ 2 + 1 := by
  rcases hs.eq_or_lt with h | hs'
  · subst h; simp
  rcases le_or_gt s 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt s hs' h1
    rw [mul_comm]; nlinarith [sq_nonneg s]
  · have hl : 0 ≤ Real.log s := Real.log_nonneg h1.le
    have hl2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs'
    rw [abs_of_nonneg (mul_nonneg hs hl)]
    nlinarith

end GaussianMatrix

open GaussianMatrix Filter Topology

theorem solution (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    ∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1)
      - (∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1) := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgcont : Continuous g := hg.continuous
  have hdcont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  obtain ⟨M1, hM1⟩ := hgcont.bounded_above_of_compact_support hgc
  obtain ⟨M2, hM2⟩ := hdcont.bounded_above_of_compact_support hgc.deriv
  set M := max M1 M2 with hMdef
  have hgM : ∀ x, |g x| ≤ M := fun x => by
    have := hM1 x; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hdM : ∀ x, |deriv g x| ≤ M := fun x => by
    have := hM2 x; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_right _ _)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hgM 0)
  have hg2M : ∀ x, g x ^ 2 ≤ M ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hgM x) 2
  have hd2M : ∀ x, deriv g x ^ 2 ≤ M ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdM x) 2
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [ε]; rw [div_le_one (by positivity)]
    linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f : ℕ → ℝ → ℝ := fun n x => g x ^ 2 + ε n
  have hf_deriv : ∀ n x, deriv (f n) x = 2 * g x * deriv g x := by
    intro n x
    have := (((hgd x).hasDerivAt.pow 2).add_const (ε n))
    exact this.deriv.trans (by simp)
  have hf_contDiff : ∀ n, ContDiff ℝ 1 (f n) := fun n => (hg.pow 2).add contDiff_const
  have hfcont : ∀ n, Continuous (f n) := fun n => (hf_contDiff n).continuous
  -- the bounded-below inequality for `f n`
  have hineq : ∀ n, ∫ x, f n x * Real.log (f n x) ∂(gaussianReal 0 1)
      - (∫ x, f n x ∂(gaussianReal 0 1)) * Real.log (∫ x, f n x ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1) := by
    intro n
    have h := gaussian_logsobolev_bounded_below (f n) (hf_contDiff n) (ε n) (3 * M ^ 2 + 1)
      (hε n) (fun x => by simp only [f]; linarith [sq_nonneg (g x)])
      (fun x => by simp only [f]; linarith [hg2M x, hε1 n, sq_nonneg M])
      (fun x => by
        rw [hf_deriv, abs_mul, abs_mul, abs_two]
        have := mul_le_mul (hgM x) (hdM x) (abs_nonneg _) hM0
        nlinarith [sq_nonneg M])
    refine h.trans ?_
    have hle : ∫ x, deriv (f n) x ^ 2 / f n x ∂(gaussianReal 0 1)
        ≤ ∫ x, 4 * deriv g x ^ 2 ∂(gaussianReal 0 1) := by
      refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
        (Eventually.of_forall (fun x => ?_))
      · exact div_nonneg (sq_nonneg _) (by simp only [f]; linarith [sq_nonneg (g x), hε n])
      · refine Integrable.mono' (integrable_const (4 * M ^ 2))
          ((hdcont.pow 2).const_mul 4).aestronglyMeasurable
          (Eventually.of_forall (fun x => ?_))
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        linarith [hd2M x]
      · simp only
        rw [hf_deriv, div_le_iff₀ (by simp only [f]; linarith [sq_nonneg (g x), hε n])]
        simp only [f]
        nlinarith [mul_nonneg (sq_nonneg (deriv g x)) (hε n).le]
    rw [integral_const_mul] at hle
    linarith
  -- limits as `n → ∞`
  have hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x ^ 2)) := fun x => by
    simpa using (tendsto_const_nhds (x := g x ^ 2)).add hεlim
  have hfb : ∀ n x, 0 ≤ f n x ∧ f n x ≤ M ^ 2 + 1 := fun n x => by
    simp only [f]; constructor <;> linarith [sq_nonneg (g x), hg2M x, hε n, hε1 n]
  have L1 : Tendsto (fun n => ∫ x, f n x ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, g t ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M ^ 2 + 1)
      (fun n => (hfcont n).aestronglyMeasurable) (integrable_const _) (fun n => ?_)
      (Eventually.of_forall hpt)
    refine Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfb n x).1]; exact (hfb n x).2
  have L2 : Tendsto (fun n => ∫ x, f n x * Real.log (f n x) ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (M ^ 2 + 1) ^ 2 + 1)
      (fun n => ((hfcont n).measurable.mul (hfcont n).measurable.log).aestronglyMeasurable)
      (integrable_const _) (fun n => ?_) ?_
    · refine Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_mul_log_le_sq_add_one _ (hfb n x).1).trans ?_
      have := pow_le_pow_left₀ (hfb n x).1 (hfb n x).2 2
      linarith
    · exact Eventually.of_forall (fun x => (Real.continuous_mul_log.tendsto _).comp (hpt x))
  have L4 : Tendsto (fun n => (∫ x, f n x ∂(gaussianReal 0 1))
        * Real.log (∫ x, f n x ∂(gaussianReal 0 1))) atTop
      (𝓝 ((∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1)))) :=
    (Real.continuous_mul_log.tendsto _).comp L1
  exact le_of_tendsto' (L2.sub L4) hineq
