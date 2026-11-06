-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.root_loss_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:40:42.60447+00:00
-- url     : https://prove2.me/submissions/2ccff384-fcb7-4290-9e89-1333171d7104

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_StoppedMass
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_Statistics_TreeMeasure
import Theorems.Thm_BianchiIX_InverseBranchTree_root_sdiff_survivors
import Theorems.Thm_BianchiIX_InverseBranchTree_stoppedDomain_measurable
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_injective
import Theorems.Thm_BianchiIX_digitPrefix_extendPositiveWord
import Theorems.Thm_BianchiIX_stopped_total_mass_le
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


theorem solution (ell : ℕ → ℝ≥0∞) (L : ℝ)
    (hK : ∀ w, T.terminal w ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ w, ∀ x ∈ T.terminal w, DifferentiableAt ℝ (T.toRoot w) x)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ell w.length)
    (hbound : ∀ w, ∀ x ∈ T.terminal w, |deriv (T.toRoot w) x| ≤
      Real.exp L * |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) :
    volume (T.root \ T.survivors) ≤ 2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m := by
  rw [survivors, T.root_sdiff_survivors]
  apply stopped_total_mass_le
    (fun m (w : {w : List ℕ+ // w.length = m}) => extendPositiveWord w.val)
    (fun m (w : {w : List ℕ+ // w.length = m}) => T.toRoot w.val)
    (fun m (w : {w : List ℕ+ // w.length = m}) => T.stoppedDomain w.val) ell L
  · intro m v w heq
    apply Subtype.ext
    apply List.map_injective_iff.mpr Subtype.val_injective
    have hv := digitPrefix_extendPositiveWord v.val
    have hw := digitPrefix_extendPositiveWord w.val
    rw [v.property] at hv
    rw [w.property] at hw
    exact hv.symm.trans (heq.trans hw)
  · exact fun _ w => T.stoppedDomain_measurable w.val
  · exact fun _ w => sdiff_subset.trans (hK w.val)
  · exact fun _ w x hx => hF w.val x hx.1
  · exact fun _ w => (T.toRoot_injective w.val).mono sdiff_subset
  · intro m w
    simpa only [w.property] using hsize w.val
  · intro m w x hx
    simpa only [← w.property, digitPrefix_extendPositiveWord] using hbound w.val x hx.1
