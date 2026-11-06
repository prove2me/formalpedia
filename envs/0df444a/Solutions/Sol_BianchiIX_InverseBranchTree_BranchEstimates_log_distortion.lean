-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.log_distortion
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:38:02.696616+00:00
-- url     : https://prove2.me/submissions/2632f967-0f56-42ed-a63c-ef3fae1f4f10

import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_terminal_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_toRoot_regular
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_nil
import Theorems.Thm_BianchiIX_gaussWord_positive_regular
import Theorems.Thm_BianchiIX_log_deriv_gaussWord_append
import Theorems.Thm_BianchiIX_log_deriv_gaussWord_lipschitz
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pos {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : 0 < gaussInv a x := by
  unfold gaussInv
  exact one_div_pos.mpr (by linarith)

end
end

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_gaussInv {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) :
    HasDerivAt (gaussInv a) (-1 / (a + x) ^ 2) x := by
  have hden : a + x ≠ 0 := ne_of_gt (by linarith)
  unfold gaussInv
  simpa only [one_div, id_eq] using ((hasDerivAt_id x).const_add a).fun_inv hden

end
end

open Set MeasureTheory
open scoped NNReal ENNReal
open BianchiIX
open BianchiIX.InverseBranchTree
open BianchiIX.InverseBranchTree.BranchEstimates
variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)
include E


theorem solution (w : List ℕ+) {x : ℝ} (hx : x ∈ T.terminal w) :
    |Real.log (|deriv (T.toRoot w) x| /
      |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|)| ≤
      ∑ j ∈ Finset.range w.length, (e j + if j = 0 then 0 else 2 * d j) := by
  induction w using List.reverseRecOn generalizing x with
  | nil => simp [gaussWord]
  | append_singleton w a ih =>
    have hterminal := hx
    rw [T.terminal_append] at hx
    have hx0 := (E.domain_subset w a hx.1).1.le
    have hy0 := (E.terminal_subset w hx.2).1.le
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast a.pos
    have hg0 := (gaussInv_pos ha hx0).le
    have hp := E.toRoot_regular w hx.2
    have hg := gaussWord_positive_regular w hy0
    have hprev := ih hx.2
    rw [Real.log_div (abs_ne_zero.mpr hp.2) (abs_ne_zero.mpr hg.2)] at hprev
    have hgn : deriv (gaussInv a) x ≠ 0 := by
      rw [(hasDerivAt_gaussInv ha hx0).deriv]
      exact div_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt (by linarith)))
    have hstep := E.log_error w a x hx.1
    rw [Real.log_div (abs_ne_zero.mpr (E.nonzero w a x hx.1)) (abs_ne_zero.mpr hgn)] at hstep
    have hphase :
        |Real.log (|deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (T.branch w a x)|) -
          Real.log (|deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (gaussInv a x)|)| ≤
          if w.length = 0 then 0 else 2 * d w.length := by
      by_cases hw : w.length = 0
      · have hz := List.length_eq_zero_iff.mp hw
        simp [hz, gaussWord]
      · rw [if_neg hw]
        exact (log_deriv_gaussWord_lipschitz w hy0 hg0).trans
          (mul_le_mul_of_nonneg_left (E.value_error w a x hx.1) (by norm_num))
    rw [Real.log_div (abs_ne_zero.mpr (E.toRoot_regular (w ++ [a]) hterminal).2)
      (abs_ne_zero.mpr (gaussWord_positive_regular (w ++ [a]) hx0).2),
      T.toRoot_append, deriv_comp x hp.1 (E.differentiable w a x hx.1), abs_mul,
      Real.log_mul (abs_ne_zero.mpr hp.2) (abs_ne_zero.mpr (E.nonzero w a x hx.1)),
      log_deriv_gaussWord_append w a hx0]
    simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
    let r := Real.log |deriv (T.toRoot w) (T.branch w a x)| -
      Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (T.branch w a x)|
    let p := Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (T.branch w a x)| -
      Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (gaussInv a x)|
    let s := Real.log |deriv (T.branch w a) x| - Real.log |deriv (gaussInv a) x|
    have hsum : Real.log |deriv (T.toRoot w) (T.branch w a x)| +
        Real.log |deriv (T.branch w a) x| -
        (Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (gaussInv a x)| +
        Real.log |deriv (gaussInv a) x|) = r + p + s := by
      dsimp [r, p, s]
      ring
    rw [hsum]
    have htri : |r + p + s| ≤ |r| + |p| + |s| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le r p) le_rfl)
    dsimp [r, p, s] at htri
    linarith
