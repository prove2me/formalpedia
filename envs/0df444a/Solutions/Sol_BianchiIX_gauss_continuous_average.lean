-- Prove2me | solution 1 for BianchiIX.gauss_continuous_average
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:24:04.369339+00:00
-- url     : https://prove2.me/submissions/97627206-f14b-42dc-bd8f-9067b3d67c22

import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_GaussContinuous
import Theorems.Thm_BianchiIX_gaussEmpiricalMass_weighted_tendsto
import Theorems.Thm_BianchiIX_gaussRepresentative_average_error
import Theorems.Thm_BianchiIX_gaussRepresentative_integral_error
import Theorems.Thm_BianchiIX_gaussRepresentative_mem_unit
import Theorems.Thm_BianchiIX_gaussRepresentative_uniform_approximation
import Theorems.Thm_BianchiIX_integrable_gauss_continuous
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


theorem solution (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (timeAverage (fun j => f (gaussMap^[j] (gaussCode a)))) atTop
      (𝓝 (∫ x, f x ∂gaussMeasure)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := gaussRepresentative_uniform_approximation hf (show 0 < ε / 3 by linarith)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hb (w : GaussWords n) : |f (gaussRepresentative n w)| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM _ (gaussRepresentative_mem_unit n w)
  have hi := gaussRepresentative_integral_error (integrable_gauss_continuous hf) n hb hn
  have hp := gaussEmpiricalMass_weighted_tendsto a ha n hb
  filter_upwards [Metric.tendsto_nhds.mp hp (ε / 3) (by linarith)] with N hN
  rw [Real.dist_eq] at hN ⊢
  have he := gaussRepresentative_average_error a n N hn
  have htri := abs_sub_le
    (timeAverage (fun j => f (gaussMap^[j] (gaussCode a))) (N + 1))
    (∑' w, gaussEmpiricalMass a n N w * f (gaussRepresentative n w))
    (∫ x, f x ∂gaussMeasure)
  have htri' := abs_sub_le
    (∑' w, gaussEmpiricalMass a n N w * f (gaussRepresentative n w))
    (∑' w, gaussMass n w * f (gaussRepresentative n w)) (∫ x, f x ∂gaussMeasure)
  rw [abs_sub_comm (∑' w, gaussMass n w * f (gaussRepresentative n w))] at htri'
  linarith
