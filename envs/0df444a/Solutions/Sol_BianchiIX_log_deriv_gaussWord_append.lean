-- Prove2me | solution 1 for BianchiIX.log_deriv_gaussWord_append
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:58:24.145786+00:00
-- url     : https://prove2.me/submissions/5e4c9293-bf1b-42d1-b29c-24797b89063d

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_gaussWord_positive_regular
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


theorem solution (w : List ℕ+) (a : ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    Real.log |deriv (gaussWord ((w ++ [a]).map (fun b : ℕ+ => (b : ℕ)))) x| =
      Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (gaussInv a x)| +
        Real.log |deriv (gaussInv a) x| := by
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast a.pos
  have hg := hasDerivAt_gaussInv ha hx
  have hp := gaussWord_positive_regular w (gaussInv_pos ha hx).le
  have hf : gaussWord ((w ++ [a]).map (fun b : ℕ+ => (b : ℕ))) =
      gaussWord (w.map (fun b : ℕ+ => (b : ℕ))) ∘ gaussInv a := by
    funext t
    simp only [List.map_append, List.map_singleton, gaussWord_append, gaussWord,
      Function.comp_apply]
  have hgn : deriv (gaussInv a) x ≠ 0 := by
    rw [hg.deriv]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt (by linarith)))
  rw [hf, deriv_comp x hp.1 hg.differentiableAt, abs_mul,
    Real.log_mul (abs_ne_zero.mpr hp.2) (abs_ne_zero.mpr hgn)]
