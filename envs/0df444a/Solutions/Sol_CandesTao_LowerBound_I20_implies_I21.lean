-- Prove2me | solution 1 for CandesTao.LowerBound.I20_implies_I21
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:36:08.089253+00:00
-- url     : https://prove2.me/submissions/deaff977-7b7a-42fb-8d26-65e6de9e4255

import Definitions.Def_CandesTao_LowerBound_SamplingConditions

namespace CandesTao.LowerBound

theorem aux_i20i21_exp_neg_le (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hprod : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]; simp
  have he : 0 < Real.exp (-x) := Real.exp_pos _
  have hqpos : 0 < 1 + x + x ^ 2 / 2 := by positivity
  have h1 : Real.exp (-x) * (1 + x + x ^ 2 / 2) ≤ 1 := by
    calc Real.exp (-x) * (1 + x + x ^ 2 / 2) ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_left hq he.le
      _ = 1 := hprod
  have h2 : 1 ≤ (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) := by
    nlinarith [sq_nonneg (x ^ 2)]
  by_contra hcon
  rw [not_le] at hcon
  have : (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) < Real.exp (-x) * (1 + x + x ^ 2 / 2) :=
    mul_lt_mul_of_pos_right hcon hqpos
  linarith

end CandesTao.LowerBound

open CandesTao.LowerBound

theorem solution
    (n m r : ℕ) (μ₀ δ : ℝ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ₀ : 1 ≤ μ₀)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (h : SamplingConditionI20 n m r μ₀ δ) :
    SamplingConditionI21 n m r μ₀ δ := by
  unfold SamplingConditionI20 at h
  unfold SamplingConditionI21 epsilonI21
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hr hrn
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn : (0 : ℝ) < n := by linarith
  set L := Real.log (n / (2 * δ)) with hLdef
  have hL : 0 < L := by
    apply Real.log_pos
    rw [one_lt_div (by positivity)]
    linarith
  set x := μ₀ * r / n * L with hxdef
  have hx : 0 ≤ x := by positivity
  have hexp : Real.exp (-(μ₀ * r / n) * L) = Real.exp (-x) := by
    rw [hxdef]; ring_nf
  rw [hexp] at h
  have hk := aux_i20i21_exp_neg_le x hx
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h3 : (n : ℝ) ^ 2 * (x - x ^ 2 / 2) ≤ (n : ℝ) ^ 2 * (1 - Real.exp (-x)) :=
    mul_le_mul_of_nonneg_left (by linarith) hn2
  have heq : (1 - 1 / 2 * (μ₀ * r / n) * L) * μ₀ * n * r * L = (n : ℝ) ^ 2 * (x - x ^ 2 / 2) := by
    rw [hxdef]; field_simp
  rw [ge_iff_le, heq]
  linarith
