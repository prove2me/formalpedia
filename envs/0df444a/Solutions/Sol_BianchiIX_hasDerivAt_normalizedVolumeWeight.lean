-- Prove2me | solution 1 for BianchiIX.hasDerivAt_normalizedVolumeWeight
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:54:47.668106+00:00
-- url     : https://prove2.me/submissions/b33bd068-bb04-437a-8fe0-24bd5812a869

import Definitions.Def_BianchiIX_Dynamics_FlowDeterminant
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_hasDerivAt_wallAmplitude
import Theorems.Thm_BianchiIX_hasDerivAt_wall_product
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology

section
open BianchiIX
noncomputable section

private theorem BianchiIX.corrected_divergence_identity
    {q s2 h : ℝ} (hconstraint : s2 + q = 1) (hh : 0 ≤ h) :
    2 * q - 4 * (-2 * s2 * h) / (1 + 4 * h) = correctedDivergence q h := by
  have hden : 1 + 4 * h ≠ 0 := by linarith
  unfold correctedDivergence
  field_simp
  nlinarith [hconstraint]

end
end

theorem solution {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t)
    (hpos : positiveWalls (α t)) (hcon : stateConstraint (α t) = 1) :
    HasDerivAt (fun u => normalizedVolumeWeight (α u))
      ((normalizedDivergence (α t) - normalizedCorrectedDivergence (α t)) *
        normalizedVolumeWeight (α t)) t := by
  obtain ⟨_, _, ha, hb, hc⟩ := hasDerivAt_normalized_components hα
  have hH := hasDerivAt_wallAmplitude (p := fun u => α u 0) (s := fun u => α u 1)
    ha hb hc hpos.1 hpos.2.1 hpos.2.2
  have hprod := hasDerivAt_wall_product (p := fun u => α u 0) (s := fun u => α u 1) ha hb hc
  have hh : 0 ≤ wallAmplitude (α t 2) (α t 3) (α t 4) :=
    Real.rpow_nonneg (mul_pos (mul_pos hpos.1 hpos.2.1) hpos.2.2).le _
  have heq := corrected_divergence_identity
    (q := curvature (α t 2) (α t 3) (α t 4))
    (s2 := shearSq (α t 0) (α t 1)) hcon hh
  have hne : 1 + 4 * wallAmplitude (α t 2) (α t 3) (α t 4) ≠ 0 := by linarith
  apply (hprod.mul ((hH.const_mul 4).const_add 1)).congr_deriv
  unfold normalizedDivergence normalizedCorrectedDivergence normalizedVolumeWeight
  rw [← heq]
  field_simp [hne]
  ring
