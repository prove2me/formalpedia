-- Prove2me | solution 1 for EulerMascheroni.P2.model_rate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:09:28.077766+00:00
-- url     : https://prove2.me/submissions/92f58087-a546-4a44-a9ab-80a1e0cb970b

import Definitions.Def_eulerMascheroni_p2Approximation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Filter Topology
open EulerMascheroni.P2

private lemma model_ratio (n : ℕ) (hn : 0 < n) :
    fModel n / qModel n = 4 * Real.pi * Real.exp
      (-rate * scale n + (2/3 : ℝ) * (1-Real.cos (3*theta)) * subscale n) := by
  have hs : scale n ≠ 0 := by
    apply ne_of_gt
    unfold scale
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hp := Real.pi_pos.ne'
  have hsq : Real.sqrt 5 ≠ 0 := by positivity
  unfold fModel qModel rate
  rw [show 5 * scale n * Real.cos theta - 2 / 3 * subscale n * Real.cos (3*theta) + 1/5 =
    (5 * scale n - 2/3 * subscale n + 1/5) +
      (- (5 * (1-Real.cos theta)) * scale n +
        2/3 * (1-Real.cos (3*theta)) * subscale n) by ring,
    Real.exp_add]
  field_simp
  <;> ring

/-- The leading exponential rate of the explicit ratio of saddle models. -/
theorem solution :
    Tendsto (fun n : ℕ => Real.log (fModel (n+1) / qModel (n+1)) / scale (n+1))
      atTop (nhds (-rate)) := by
  have ht : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hs : Tendsto (fun n : ℕ => scale (n+1)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/5)).comp ht
  have hh : Tendsto (fun n : ℕ => subscale (n+1) / scale (n+1)) atTop (nhds 0) := by
    have hx := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2/5)).comp ht
    convert hx using 1
    funext n
    unfold subscale scale
    rw [← Real.rpow_sub (by positivity : (0 : ℝ) < (n+1 : ℕ))]
    norm_num
  have hlim := (hs.const_div_atTop (Real.log (4 * Real.pi))).add
    (hh.const_mul ((2/3 : ℝ) * (1 - Real.cos (3*theta))))
  have hlim2 := hlim.add_const (-rate)
  convert hlim2 using 1
  · funext n
    rw [model_ratio (n+1) (Nat.succ_pos n),
      Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
    have hsn : scale (n+1) ≠ 0 := by unfold scale; positivity
    field_simp
    <;> ring
  · simp

#print axioms solution
