-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.ae_code_property
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:54:22.835765+00:00
-- url     : https://prove2.me/submissions/b3ffa960-2c10-4719-ad70-6019ae67920c

import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_code_map_le
import Theorems.Thm_BianchiIX_InverseBranchTree_code_measurable
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
open BianchiIX.InverseBranchTree.BranchEstimates
variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)
include E


theorem solution {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    {P : ℝ → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), P (T.code x) := by
  have hac : Measure.map T.code (volume.comap (Subtype.val : T.survivors → ℝ)) ≪ volume := by
    intro s hs
    have h := Measure.le_iff'.mp (E.code_map_le hbudget) s
    simpa only [Measure.smul_apply, hs, smul_zero, nonpos_iff_eq_zero] using h
  exact ae_of_ae_map T.code_measurable.aemeasurable (hac.ae_le hP)
