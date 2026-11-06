-- Prove2me | solution 1 for BianchiIX.eraStatistics_of_typical_code
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:11:38.031486+00:00
-- url     : https://prove2.me/submissions/c6e1895f-166c-44a3-bae0-82eeab1a2a3b

import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Theorems.Thm_BianchiIX_continuous_timeAverage_transfer
import Theorems.Thm_BianchiIX_gaussCode_shadowing
import Theorems.Thm_BianchiIX_gaussMap_iterate_code
import Theorems.Thm_BianchiIX_gauss_continuous_average
import Theorems.Thm_BianchiIX_gauss_digit_average_tendsto_atTop
import Theorems.Thm_BianchiIX_gauss_digit_block_frequency
import Theorems.Thm_BianchiIX_gauss_digit_frequency
import Theorems.Thm_BianchiIX_gauss_digit_tail_frequency
import Theorems.Thm_BianchiIX_gauss_truncated_digit_average
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_tendsto (a : ℕ → ℕ+) : Tendsto (gaussApprox a) atTop (𝓝 (gaussCode a)) :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose_spec

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_mem_unit (a : ℕ → ℕ+) : gaussCode a ∈ Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (gaussCode_tendsto a) (Eventually.of_forall (gaussApprox_mem_unit a))

end
end

theorem solution (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    {y : ℕ → ℝ} (hy : ∀ n, y n ∈ Icc (0 : ℝ) 1)
    (herror : Tendsto (inverseError (fun n => (a n : ℕ)) y) atTop (𝓝 0)) :
    EraStatistics a y := by
  refine ⟨?_, fun w hw => gauss_digit_block_frequency a ha w hw,
    gauss_digit_frequency a ha, gauss_digit_tail_frequency a ha,
    gauss_truncated_digit_average a ha, gauss_digit_average_tendsto_atTop a ha⟩
  intro f hf
  apply continuous_timeAverage_transfer isCompact_Icc hf hy _
    (gaussCode_shadowing a hy herror) (gauss_continuous_average a ha hf)
  intro n
  simpa only [gaussMap_iterate_code] using gaussCode_mem_unit (shiftDigits a n)
