-- Prove2me | solution 1 for BianchiIX.gaussCode_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T14:42:11.620418+00:00
-- url     : https://prove2.me/submissions/48d3eb54-5a11-48ad-8171-b7da856bf000

import Definitions.Def_BianchiIX_Statistics_GaussCoding
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

open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

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

private theorem BianchiIX.digitPrefix_succ (a : ℕ → ℕ+) (n : ℕ) :
    digitPrefix a (n + 1) = (a 0 : ℕ) :: digitPrefix (shiftDigits a 1) n := by
  simp [digitPrefix, List.range_succ_eq_map, List.map_map, Function.comp_def, shiftDigits,
    Nat.add_comm]

private theorem BianchiIX.gaussApprox_succ (a : ℕ → ℕ+) (n : ℕ) :
    gaussApprox a (n + 1) = gaussInv (a 0) (gaussApprox (shiftDigits a 1) n) := by
  simp only [gaussApprox, digitPrefix_succ, gaussWord]

private theorem BianchiIX.gaussCode_tendsto (a : ℕ → ℕ+) : Tendsto (gaussApprox a) atTop (𝓝 (gaussCode a)) :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose_spec

private theorem BianchiIX.gaussCode_mem_unit (a : ℕ → ℕ+) : gaussCode a ∈ Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (gaussCode_tendsto a) (Eventually.of_forall (gaussApprox_mem_unit a))

theorem solution (a : ℕ → ℕ+) :
    gaussCode a = gaussInv (a 0) (gaussCode (shiftDigits a 1)) := by
  have ha : (1 : ℝ) ≤ a 0 := by exact_mod_cast Nat.succ_le_of_lt (a 0).pos
  have h := (hasDerivAt_gaussInv ha (gaussCode_mem_unit (shiftDigits a 1)).1).continuousAt.tendsto.comp
    (gaussCode_tendsto (shiftDigits a 1))
  apply tendsto_nhds_unique ((gaussCode_tendsto a).comp (tendsto_add_atTop_nat 1))
  simpa only [Function.comp_def, gaussApprox_succ] using h
