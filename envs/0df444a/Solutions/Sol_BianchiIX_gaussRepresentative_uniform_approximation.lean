-- Prove2me | solution 1 for BianchiIX.gaussRepresentative_uniform_approximation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:15:06.105206+00:00
-- url     : https://prove2.me/submissions/c743ae14-c3d4-4af0-bac5-315a10d3706d

import Definitions.Def_BianchiIX_Statistics_GaussContinuous
import Theorems.Thm_BianchiIX_gaussCylinder_distance_representative
import Theorems.Thm_BianchiIX_gaussRepresentative_mem_unit
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
open scoped Topology ENNReal
open BianchiIX
noncomputable section
open InverseBranchTree.BranchEstimates


theorem solution {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∀ (w : GaussWords n) x, x ∈ gaussCylinder w.val →
      |f x - f (gaussRepresentative n w)| ≤ ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  obtain ⟨n, hn⟩ := ((tendsto_order.mp gauss_diameter_tendsto_zero).2 δ hδ).exists
  refine ⟨n, fun w x hx => ?_⟩
  have hxunit : x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨t, ht, rfl⟩ := hx
    exact gaussWord_mem_unit w.val w.property.2 ⟨ht.1.le, ht.2.le⟩
  have hdist : dist x (gaussRepresentative n w) < δ := by
    rw [Real.dist_eq]
    exact (gaussCylinder_distance_representative n w hx).trans_lt hn
  simpa only [Real.dist_eq] using
    (hclose x hxunit (gaussRepresentative n w) (gaussRepresentative_mem_unit n w) hdist).le
