-- Prove2me | solution 1 for BianchiIX.projectiveField_boundary_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:55:01.937305+00:00
-- url     : https://prove2.me/submissions/18c60b9f-a004-45df-863c-a66fcf951bf0

import Definitions.Def_BianchiIX_Dynamics_ProjectiveLinearization
import Theorems.Thm_BianchiIX_contDiff_projectiveField
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveField_boundary
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX


theorem solution (m v : ℝ) (xi : ProjectiveState) :
    fderiv ℝ projectiveField ![m, 0, v, 0] xi = projectiveBoundaryVariation m v xi := by
  have hl : HasDerivAt (fun s : ℝ => ![m, 0, v, 0] + s • xi) xi 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (![m, 0, v, 0] : ProjectiveState)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const xi) using 1
    simp
  have hb : (![m, 0, v, 0] : ProjectiveState) + (0 : ℝ) • xi = ![m, 0, v, 0] := by simp
  have hf := ((contDiff_projectiveField 1).differentiable (by norm_num) ![m, 0, v, 0]).hasFDerivAt
  have hf' := (hb.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hb] using hf'.unique (hasDerivAt_projectiveField_boundary hl hb)
