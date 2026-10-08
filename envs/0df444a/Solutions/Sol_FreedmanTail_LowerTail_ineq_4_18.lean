-- Prove2me | solution 1 for FreedmanTail.LowerTail.ineq_4_18
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:15:20.069632+00:00
-- url     : https://prove2.me/submissions/0111a23d-0edf-4c11-bb39-64108b2b4011

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory


namespace FreedmanTail.LowerTail

lemma e_nonneg (lam : ℝ) : 0 ≤ e lam := by
  unfold e; have := Real.add_one_le_exp lam; linarith

lemma e_le_cubic {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : e t ≤ t ^ 2 / 2 + 2 * t ^ 3 / 9 := by
  have := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at this
  unfold e; norm_num at this ⊢; nlinarith

lemma chernoff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (a : ℝ)
    (hU : LaplaceUpper P W a) (x : ℝ) (μ : ℝ) (hμ : 0 ≤ μ) :
    P.real {ω | W ω < x} ≤ Real.exp (e μ * x - μ * a) := by
  have hint : Integrable (fun ω => Real.exp (-(e μ * W ω))) P := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Real.measurable_exp.comp ((measurable_const.mul hW).neg)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have := mul_nonneg (e_nonneg μ) (hW0 ω); linarith
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => Real.exp (-(e μ * W ω)))
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hint (Real.exp (-(e μ * x)))
  have hsub : {ω | W ω < x} ⊆ {ω | Real.exp (-(e μ * x)) ≤ Real.exp (-(e μ * W ω))} := by
    intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hω.le (e_nonneg μ); linarith
  have h1 : P.real {ω | W ω < x} ≤
      P.real {ω | Real.exp (-(e μ * x)) ≤ Real.exp (-(e μ * W ω))} := measureReal_mono hsub
  have h2 := hU μ hμ
  have hε : 0 < Real.exp (-(e μ * x)) := Real.exp_pos _
  have h3 : Real.exp (-(e μ * x)) * P.real {ω | W ω < x} ≤ Real.exp (-(μ * a)) := by
    calc _ ≤ Real.exp (-(e μ * x)) *
          P.real {ω | Real.exp (-(e μ * x)) ≤ Real.exp (-(e μ * W ω))} :=
          mul_le_mul_of_nonneg_left h1 hε.le
      _ ≤ _ := hM
      _ ≤ _ := h2
  rw [show Real.exp (e μ * x - μ * a) = Real.exp (-(μ * a)) / Real.exp (-(e μ * x)) by
    rw [← Real.exp_sub]; ring_nf]
  rw [le_div_iff₀ hε]; linarith [h3]

theorem ineq_4_18_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (a : ℝ) (ha : 0 < a)
    (hU : LaplaceUpper P W a) (x : ℝ) (hx : 0 ≤ x) :
    P.real {ω | W ω < x} < Real.exp (-(a ^ 2 / (2 * (a + x)))) := by
  have hax : 0 < a + x := by linarith
  set t := a / (a + x) with ht
  have ht0 : 0 < t := div_pos ha hax
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hax]; linarith
  have hC := chernoff P W hW hW0 a hU x t ht0.le
  refine lt_of_le_of_lt hC ?_
  apply Real.exp_lt_exp.mpr
  have he := e_le_cubic ht0.le ht1
  have htx : t * (a + x) = a := by rw [ht]; field_simp
  have hgoal : a ^ 2 / (2 * (a + x)) = t * a / 2 := by rw [ht]; field_simp
  rw [hgoal]
  have h1 : e t * x ≤ (t ^ 2 / 2 + 2 * t ^ 3 / 9) * x := mul_le_mul_of_nonneg_right he hx
  have h2 : (t ^ 2 / 2 + 2 * t ^ 3 / 9) * x < t * a / 2 := by
    have : (t ^ 2 / 2 + 2 * t ^ 3 / 9) * x = (t * x) * (t / 2 + 2 * t ^ 2 / 9) := by ring
    rw [this]
    have htx' : t * x = a - t * a := by linarith [htx]
    rw [htx']
    nlinarith [mul_pos (mul_pos ht0 ht0) ha, mul_pos (mul_pos (mul_pos ht0 ht0) ht0) ha]
  linarith

end FreedmanTail.LowerTail

open FreedmanTail.LowerTail


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (a : ℝ) (ha : 0 < a)
    (hU : LaplaceUpper P W a) (x : ℝ) (hx : 0 ≤ x) :
    P.real {ω | W ω < x} < Real.exp (-(a ^ 2 / (2 * (a + x)))) := by
  exact ineq_4_18_core P W hW hW0 a ha hU x hx
