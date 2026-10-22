-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_outward_positive_of_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:07.935273+00:00
-- url     : https://prove2.me/submissions/f7779647-556f-482a-97b6-d3bb698d4a29

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue


open BirkhoffGlobalSection


open BirkhoffGlobalSection NormedSpace Set Metric Filter
open scoped Topology unitInterval BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem solution (F : Phase → ℝ) (s b : Phase) (r t : ℝ)
    (ht : 1 < t) (hb : b ∈ Metric.ball s r) (hy : t • b ∈ Metric.ball s r)
    (hFb : F b = 0)
    (hball : ∀ z ∈ Metric.ball s r, DifferentiableAt ℝ F z ∧ 0 < fderiv ℝ F z z) :
    0 < F (t • b) := by
  have htden : 0 < t - 1 := by linarith
  have hpoints : ∀ u ∈ Set.Icc (1 : ℝ) t, u • b ∈ Metric.ball s r := by
    intro u hu
    let β := (u - 1) / (t - 1)
    have hβ0 : 0 ≤ β := div_nonneg (sub_nonneg.mpr hu.1) htden.le
    have hβ1 : β ≤ 1 := (div_le_one htden).mpr (sub_le_sub_right hu.2 1)
    have hmem := (convex_ball s r) hb hy (sub_nonneg.mpr hβ1) hβ0
      (show (1 - β) + β = 1 by ring)
    have hden : β * (t - 1) = u - 1 := div_mul_cancel₀ _ htden.ne'
    have heq : (1 - β) • b + β • (t • b) = u • b := by
      rw [smul_smul, ← add_smul]
      congr 1
      nlinarith
    rw [heq] at hmem
    exact hmem
  let f : ℝ → ℝ := fun u => F (u • b)
  have hderiv : ∀ u ∈ Set.Icc (1 : ℝ) t,
      HasDerivAt f (fderiv ℝ F (u • b) b) u := by
    intro u hu
    have hP : HasDerivAt (fun a : ℝ => a • b) b u := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id u).smul_const b
    exact (hball _ (hpoints u hu)).1.hasFDerivAt.comp_hasDerivAt u hP
  have hpositive : ∀ u ∈ Set.Icc (1 : ℝ) t, 0 < fderiv ℝ F (u • b) b := by
    intro u hu
    have hpos := (hball _ (hpoints u hu)).2
    have heq : fderiv ℝ F (u • b) (u • b) = u * fderiv ℝ F (u • b) b := by
      rw [map_smul, smul_eq_mul]
    rw [heq] at hpos
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    nlinarith
  have hf : ContinuousOn f (Set.Icc (1 : ℝ) t) :=
    fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Set.Icc (1 : ℝ) t) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hf (fun u hu => by
      have hu' := interior_subset hu
      rw [(hderiv u hu').deriv]
      exact hpositive u hu')
  have hlt := hmono ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht
  simpa only [f, one_smul, hFb] using hlt
