-- Prove2me | solution 1 for BianchiIX.measurable_gaussCode
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T14:42:59.695307+00:00
-- url     : https://prove2.me/submissions/ef854d0f-44d4-4394-9ec1-98534e0ecad1

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

private theorem BianchiIX.digitPrefix_succ (a : ℕ → ℕ+) (n : ℕ) :
    digitPrefix a (n + 1) = (a 0 : ℕ) :: digitPrefix (shiftDigits a 1) n := by
  simp [digitPrefix, List.range_succ_eq_map, List.map_map, Function.comp_def, shiftDigits,
    Nat.add_comm]

private theorem BianchiIX.gaussApprox_succ (a : ℕ → ℕ+) (n : ℕ) :
    gaussApprox a (n + 1) = gaussInv (a 0) (gaussApprox (shiftDigits a 1) n) := by
  simp only [gaussApprox, digitPrefix_succ, gaussWord]

private theorem BianchiIX.gaussCode_tendsto (a : ℕ → ℕ+) : Tendsto (gaussApprox a) atTop (𝓝 (gaussCode a)) :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose_spec

private theorem BianchiIX.measurable_gaussApprox (n : ℕ) : Measurable (fun a : ℕ → ℕ+ => gaussApprox a n) := by
  induction n with
  | zero => simp [gaussApprox, digitPrefix, gaussWord]
  | succ n ih =>
    have hshift : Measurable (fun a : ℕ → ℕ+ => shiftDigits a 1) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (1 + i))
    have hcast : Measurable (fun k : ℕ+ => (k : ℝ)) := measurable_of_countable _
    have h := (measurable_const (a := (1 : ℝ))).div
      ((hcast.comp (measurable_pi_apply 0)).add (ih.comp hshift))
    simpa only [gaussApprox_succ, gaussInv, Pi.div_def, Pi.add_def,
      Function.comp_def] using h

theorem solution : Measurable gaussCode :=
  measurable_of_tendsto_metrizable measurable_gaussApprox
    (tendsto_pi_nhds.mpr gaussCode_tendsto)
