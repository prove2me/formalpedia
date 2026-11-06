-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.restricted_root_loss_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:45:02.443638+00:00
-- url     : https://prove2.me/submissions/15461f24-d872-422e-bd9e-799df993f4aa

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_Statistics_TreeMeasure
import Theorems.Thm_BianchiIX_InverseBranchTree_root_loss_le
import Theorems.Thm_BianchiIX_restricted_stopped_mass_le
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


theorem solution (I : Set ℝ) (ell : ℕ → ℝ≥0∞) (L : ℝ)
    (hK : ∀ w, T.terminal w ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ w, ∀ x ∈ T.terminal w, DifferentiableAt ℝ (T.toRoot w) x)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ell w.length)
    (hbound : ∀ w, ∀ x ∈ T.terminal w, |deriv (T.toRoot w) x| ≤
      Real.exp L * |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) :
    volume ((I ∩ T.root) \ (I ∩ T.survivors)) ≤
      min (volume I) (2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m) := by
  have heq : (I ∩ T.root) \ (I ∩ T.survivors) = I ∩ (T.root \ T.survivors) := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [heq]
  exact restricted_stopped_mass_le (T.root_loss_le ell L hK hF hsize hbound)
