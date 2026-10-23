-- Prove2me | solution 1 for CourierDispatch.Endogenous.strict_concavity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T21:37:34.388299+00:00
-- url     : https://prove2.me/submissions/c0b28569-4c05-4fc5-9d1e-132963a3eb92

import Mathlib
import Definitions.Def_CourierDispatch_Endogenous_Setting

open CourierDispatch.Exogenous CourierDispatch.Endogenous

namespace CD2Aux

lemma inv_strict (u v a b : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) : 1 / (a * u + b * v) < a * (1 / u) + b * (1 / v) := by
  have hw : 0 < a * u + b * v := by positivity
  have key : a * (1 / u) + b * (1 / v) - 1 / (a * u + b * v) =
      a * b * (u - v) ^ 2 / (u * v * (a * u + b * v)) := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    field_simp
    ring
  have : 0 < a * b * (u - v) ^ 2 / (u * v * (a * u + b * v)) := by
    have : 0 < (u - v) ^ 2 := by
      have : u - v ≠ 0 := sub_ne_zero.2 huv
      positivity
    positivity
  linarith

lemma strictConc_gen (s : Set ℝ) (hs : Convex ℝ s) (f : ℝ → ℝ) (A B K M : ℝ) (hK : 0 < K)
    (hsub : ∀ x ∈ s, x < M) (hf : ∀ x ∈ s, f x = A * x + B - K / (M - x)) :
    StrictConcaveOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hz : a • x + b • y ∈ s := hs hx hy ha.le hb.le hab
  rw [hf x hx, hf y hy, hf _ hz]
  simp only [smul_eq_mul]
  have hu : 0 < M - x := by linarith [hsub x hx]
  have hv : 0 < M - y := by linarith [hsub y hy]
  have huv : M - x ≠ M - y := by intro h; apply hxy; linarith
  have h := inv_strict (M - x) (M - y) a b hu hv huv ha hb hab
  have e : M - (a * x + b * y) = a * (M - x) + b * (M - y) := by
    have : M = (a + b) * M := by rw [hab, one_mul]
    linarith [this]
  rw [e]
  have e1 : K / (a * (M - x) + b * (M - y)) = K * (1 / (a * (M - x) + b * (M - y))) := by ring
  have e2 : K / (M - x) = K * (1 / (M - x)) := by ring
  have e3 : K / (M - y) = K * (1 / (M - y)) := by ring
  rw [e1, e2, e3]
  have := mul_lt_mul_of_pos_left h hK
  have hB' : a * B + b * B = B := by rw [← add_mul, hab, one_mul]
  nlinarith [this, hB']

lemma ms_strict_concavity (CB c r : ℝ) (hCB : 0 < CB) (hc : 0 < c) (hr : 0 < r) :
    StrictConcaveOn ℝ (domD r) (VinfD c r) ∧ StrictConcaveOn ℝ (domB r) (VinfB CB c r) := by
  have hCD : (0:ℝ) < CD := by unfold CD; norm_num
  constructor
  · have hμ : 0 < muD r := by unfold muD; positivity
    have hk : 0 < c * CD / (2 * muD r) := div_pos (mul_pos hc hCD) (by positivity)
    apply strictConc_gen (domD r) (convex_Ico _ _) _ (1 + c * CD / (2 * muD r))
      (c * CD / (2 * muD r) * muD r) (c * CD / (2 * muD r) * muD r ^ 2) (muD r) (by positivity)
    · intro x hx; exact hx.2
    · intro x hx
      have hx2 : x < muD r := hx.2
      have hne : muD r - x ≠ 0 := by linarith
      have hne' : muD r ≠ 0 := hμ.ne'
      unfold VinfD Vinf WD
      field_simp
      ring
  · have hμ : 0 < muB r := by unfold muB; positivity
    have hk : 0 < c * CB / (2 * muB r) := div_pos (mul_pos hc hCB) (by positivity)
    apply strictConc_gen (domB r) (convex_Ioo _ _) _ (1 - c * r / 3 + c * CB / (2 * muB r))
      (c * CB / (2 * muB r) * (2 * muB r) - c / 2)
      (c * CB / (2 * muB r) * (2 * muB r) ^ 2) (2 * muB r) (by positivity)
    · intro x hx; exact hx.2
    · intro x hx
      have hx0 : 0 < x := hx.1
      have hx2 : x < 2 * muB r := hx.2
      have hne : 2 * muB r - x ≠ 0 := by linarith
      have hne' : muB r ≠ 0 := hμ.ne'
      have hx0' : x ≠ 0 := hx0.ne'
      unfold VinfB Vinf WB
      field_simp
      ring

end CD2Aux

theorem solution (CB c r : ℝ) (hCB : 0 < CB) (hc : 0 < c) (hr : 0 < r) :
    StrictConcaveOn ℝ (domD r) (VinfD c r) ∧
    StrictConcaveOn ℝ (domB r) (VinfB CB c r) := by
  exact CD2Aux.ms_strict_concavity CB c r hCB hc hr
