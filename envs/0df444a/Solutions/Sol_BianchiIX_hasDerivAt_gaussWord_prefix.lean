-- Prove2me | solution 1 for BianchiIX.hasDerivAt_gaussWord_prefix
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:19:02.777364+00:00
-- url     : https://prove2.me/submissions/38058b41-5714-4500-b2b7-3eb28ee01e8c

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussDistortion
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

open BianchiIX
noncomputable section
open Set Finset

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

private theorem BianchiIX.gaussDenom_succ (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gaussDenom a (n + 1) x = gaussDenom a n (gaussInv (a n) x) * ((a n : ℝ) + x) := by
  have ha : (1 : ℝ) ≤ a n := by exact_mod_cast Nat.succ_le_of_lt (a n).pos
  have hax : (a n : ℝ) + x ≠ 0 := ne_of_gt (by linarith)
  dsimp [gaussDenom, gaussDenoms, gaussInv]
  field_simp
  ring

private theorem BianchiIX.gaussWord_prefix_succ (a : ℕ → ℕ+) (n : ℕ) (x : ℝ) :
    gaussWord (digitPrefix a (n + 1)) x =
      gaussWord (digitPrefix a n) (gaussInv (a n) x) := by
  rw [digitPrefix_add, gaussWord_append]
  simp [digitPrefix, shiftDigits, gaussWord]

theorem solution (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (gaussWord (digitPrefix a n))
      ((-1 : ℝ) ^ n / (gaussDenom a n x) ^ 2) x := by
  induction n generalizing x with
  | zero =>
    convert! (hasDerivAt_id x) using 1
    norm_num [gaussDenom, gaussDenoms]
  | succ n ih =>
    have ha : (1 : ℝ) ≤ a n := by exact_mod_cast Nat.succ_le_of_lt (a n).pos
    have hg := hasDerivAt_gaussInv ha hx
    have hp := ih (gaussInv_pos ha hx).le
    have h := hp.comp x hg
    have hf : gaussWord (digitPrefix a (n + 1)) =
        fun t => gaussWord (digitPrefix a n) (gaussInv (a n) t) := by
      funext t
      exact gaussWord_prefix_succ a n t
    rw [hf]
    convert! h using 1
    rw [gaussDenom_succ a n hx, pow_succ, mul_pow, div_mul_div_comm]
