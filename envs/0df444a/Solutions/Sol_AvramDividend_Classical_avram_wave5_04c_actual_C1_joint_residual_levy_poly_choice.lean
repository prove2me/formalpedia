-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:50:02.497816+00:00
-- url     : https://prove2.me/submissions/df023254-f1a6-42ca-a2de-961f088070af

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_global_weighted_Bernstein_payoff_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

/-! A single C1 exponential polynomial simultaneously controls original
BV residual expectations and the original negative Levy generator integral. -/
theorem solution (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      (∀ r : ℝ, 0 ≤ r →
        |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
          ε * (1 - Real.exp (-r)) +
            (if M < r then 2 * |w x - w (x - r)| else 0)) ∧
      (∀ y : ℝ, y < 0 →
        |Polynomial.eval (Real.exp y) Q - (w x - w (x + y))| ≤
          ε * (1 - Real.exp y) +
            (if y < -M then 2 * |w x - w (x + y)| else 0)) := by
  let a : ℝ := Real.exp (-(M + 1))
  let b : ℝ := Real.exp (-M)
  have ha : 0 < a := Real.exp_pos _
  have hab : a < b := by
    dsimp [a, b]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hb : b ≤ 1 := by
    dsimp [b]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨Q, hQ, hQT⟩ :=
    avram_wave5_04c_actual_C1_global_weighted_Bernstein_payoff_tail
      w hw x a b ε ha hab hb hε
  have hR (r : ℝ) (hr : 0 ≤ r) :
      |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
        ε * (1 - Real.exp (-r)) +
          (if M < r then 2 * |w x - w (x - r)| else 0) := by
    have he0 : 0 < Real.exp (-r) := Real.exp_pos _
    have he1 : Real.exp (-r) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    let t : unitInterval.Elem := ⟨Real.exp (-r), ⟨he0.le, he1⟩⟩
    have ht : (t : ℝ) = Real.exp (-r) := rfl
    have hlog : Real.log (t : ℝ) = -r := by rw [ht, Real.log_exp]
    have hcut : ((t : ℝ) < b) ↔ M < r := by
      rw [ht]
      dsimp [b]
      rw [Real.exp_lt_exp]
      constructor <;> intro h <;> linarith
    have h := hQT t (by simpa only [ht] using he0)
    rw [hlog] at h
    simp only [hcut] at h
    simpa only [ht, sub_eq_add_neg] using h
  refine ⟨Q, hQ, hR, ?_⟩
  intro y hy
  have h := hR (-y) (by linarith)
  have hx : x - -y = x + y := by ring
  have ht : (M < -y) ↔ y < -M := by constructor <;> intro h <;> linarith
  simpa only [neg_neg, hx, ht] using h
