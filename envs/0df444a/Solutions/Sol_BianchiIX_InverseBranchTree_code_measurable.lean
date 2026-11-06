-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.code_measurable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:46:07.660051+00:00
-- url     : https://prove2.me/submissions/0a8d8068-9a09-4596-9d34-ecd84dd6343a

import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Theorems.Thm_BianchiIX_InverseBranchTree_digits_measurable
import Theorems.Thm_BianchiIX_measurable_gaussCode
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


open Set MeasureTheory
open scoped NNReal ENNReal
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)


theorem solution : Measurable T.code := measurable_gaussCode.comp T.digits_measurable
