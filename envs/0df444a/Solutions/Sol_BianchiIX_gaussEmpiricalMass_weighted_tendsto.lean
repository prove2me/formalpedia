-- Prove2me | solution 1 for BianchiIX.gaussEmpiricalMass_weighted_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:22:12.833209+00:00
-- url     : https://prove2.me/submissions/529487e9-c08a-4009-b5b3-9a88e83a15ce

import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_GaussPartition
import Theorems.Thm_BianchiIX_empiricalMass_hasSum
import Theorems.Thm_BianchiIX_empiricalMass_nonneg
import Theorems.Thm_BianchiIX_gaussEmpiricalMass_tendsto
import Theorems.Thm_BianchiIX_gaussMass_hasSum
import Theorems.Thm_BianchiIX_gaussMass_nonneg
import Theorems.Thm_BianchiIX_probability_weighted_tendsto
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

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section


theorem solution (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (n : ℕ) {f : GaussWords n → ℝ} {M : ℝ} (hf : ∀ w, |f w| ≤ M) :
    Tendsto (fun N => ∑' w, gaussEmpiricalMass a n N w * f w)
      atTop (𝓝 (∑' w, gaussMass n w * f w)) :=
  probability_weighted_tendsto (fun N w => empiricalMass_nonneg _ N w) (gaussMass_nonneg n)
    (fun N => empiricalMass_hasSum _ N) (gaussMass_hasSum n) (gaussEmpiricalMass_tendsto a ha n) hf
