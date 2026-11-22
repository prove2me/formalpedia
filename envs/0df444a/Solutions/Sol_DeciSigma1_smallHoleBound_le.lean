-- Prove2me | solution 1 for DeciSigma1.smallHoleBound_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:31:16.052002+00:00
-- url     : https://prove2.me/submissions/991f4993-114d-4c45-9138-5e00c24d8406

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_double_exp2_pow_le
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_iterate_exp2_add_le
public import Theorems.Thm_DeciSigma1_Arithmetic_iterate_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_iterate_exp2_mul_le
public import Theorems.Thm_DeciSigma1_Arithmetic_le_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_le_iterate_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_succ_le_exp2
public import Theorems.Thm_DeciSigma1_Automata_lowerRun_nil
public import Theorems.Thm_DeciSigma1_Automata_lowerRun_snoc
public import Theorems.Thm_DeciSigma1_Automata_mem_down
public import Theorems.Thm_DeciSigma1_Automata_mem_lowerStep
public import Theorems.Thm_DeciSigma1_Automata_mem_up
public import Theorems.Thm_DeciSigma1_Automata_mem_upperStep
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Automata_upperRun_snoc
public import Theorems.Thm_DeciSigma1_Automata_upperStep_empty
public import Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_extend_fresh
public import Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_extend_original
public import Theorems.Thm_DeciSigma1_Constraints_base_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_dual_eq_bot
public import Theorems.Thm_DeciSigma1_Constraints_dual_eq_top
public import Theorems.Thm_DeciSigma1_Constraints_holdsT_map
public import Theorems.Thm_DeciSigma1_Constraints_holds_false
public import Theorems.Thm_DeciSigma1_Constraints_lowerAt_nil_iff
public import Theorems.Thm_DeciSigma1_Constraints_normalize_false_eq_bot
public import Theorems.Thm_DeciSigma1_Constraints_normalize_false_eq_top
public import Theorems.Thm_DeciSigma1_Constraints_normalize_not
public import Theorems.Thm_DeciSigma1_Constraints_normalized_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_sat_append
public import Theorems.Thm_DeciSigma1_Constraints_sat_cons
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Constraints_sat_lift
public import Theorems.Thm_DeciSigma1_Constraints_sat_signed_iff
public import Theorems.Thm_DeciSigma1_Constraints_sign_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_signedDual_signedVar
public import Theorems.Thm_DeciSigma1_Constraints_signedVar_base_sign
public import Theorems.Thm_DeciSigma1_Constraints_upperAt_nil_iff
public import Theorems.Thm_DeciSigma1_Full_Closure_configSet_assignmentOf
public import Theorems.Thm_DeciSigma1_Full_Closure_flipEmb_apply
public import Theorems.Thm_DeciSigma1_Full_Closure_mem_factList
public import Theorems.Thm_DeciSigma1_Full_Closure_mem_negList
public import Theorems.Thm_DeciSigma1_Full_Models_GroundBound_holds_map
public import Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_nonBottomPrefixes_realize
public import Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_symmetrize_toTree
public import Theorems.Thm_DeciSigma1_Holes_Fresh_freshTupleBound_le_double_exp2
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_tailLengthBound_le_double_exp2
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_holds_append
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_selectedShape_domain
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_fn_nil
public import Theorems.Thm_DeciSigma1_Semantics_FTree_height_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_height_top
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
public import Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_extendedLabel_toTree_nil
public import Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_median_toTree
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_positions_toTree
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_eq_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_le_toTree
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_mix_fn
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_cons
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_top
public import Theorems.Thm_DeciSigma1_Semantics_bot_treeLe
public import Theorems.Thm_DeciSigma1_Semantics_dual_bot
public import Theorems.Thm_DeciSigma1_Semantics_dual_fn
public import Theorems.Thm_DeciSigma1_Semantics_dual_involutive
public import Theorems.Thm_DeciSigma1_Semantics_dual_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_dual_node
public import Theorems.Thm_DeciSigma1_Semantics_dual_top
public import Theorems.Thm_DeciSigma1_Semantics_fullTree_fn
public import Theorems.Thm_DeciSigma1_Semantics_node_treeLe_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_normalize_bot
public import Theorems.Thm_DeciSigma1_Semantics_normalize_false_variance
public import Theorems.Thm_DeciSigma1_Semantics_normalize_fn
public import Theorems.Thm_DeciSigma1_Semantics_normalize_involutive
public import Theorems.Thm_DeciSigma1_Semantics_normalize_node
public import Theorems.Thm_DeciSigma1_Semantics_normalize_top
public import Theorems.Thm_DeciSigma1_Semantics_normalize_true
public import Theorems.Thm_DeciSigma1_Semantics_top_treeLe_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_false_iff_le
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_top
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.lowerRun_nil
attribute [local simp] DeciSigma1.Automata.lowerRun_snoc
attribute [local simp] DeciSigma1.Automata.mem_down
attribute [local simp] DeciSigma1.Automata.mem_lowerStep
attribute [local simp] DeciSigma1.Automata.mem_up
attribute [local simp] DeciSigma1.Automata.mem_upperStep
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Automata.upperRun_snoc
attribute [local simp] DeciSigma1.Automata.upperStep_empty
attribute [local simp] DeciSigma1.Constraints.GroundCompiler.extend_fresh
attribute [local simp] DeciSigma1.Constraints.GroundCompiler.extend_original
attribute [local simp] DeciSigma1.Constraints.base_signedVar
attribute [local simp] DeciSigma1.Constraints.dual_eq_bot
attribute [local simp] DeciSigma1.Constraints.dual_eq_top
attribute [local simp] DeciSigma1.Constraints.holdsT_map
attribute [local simp] DeciSigma1.Constraints.holds_false
attribute [local simp] DeciSigma1.Constraints.lowerAt_nil_iff
attribute [local simp] DeciSigma1.Constraints.normalize_false_eq_bot
attribute [local simp] DeciSigma1.Constraints.normalize_false_eq_top
attribute [local simp] DeciSigma1.Constraints.normalize_not
attribute [local simp] DeciSigma1.Constraints.normalized_signedVar
attribute [local simp] DeciSigma1.Constraints.sat_append
attribute [local simp] DeciSigma1.Constraints.sat_cons
attribute [local simp] DeciSigma1.Constraints.sat_false
attribute [local simp] DeciSigma1.Constraints.sat_lift
attribute [local simp] DeciSigma1.Constraints.sat_signed_iff
attribute [local simp] DeciSigma1.Constraints.sign_signedVar
attribute [local simp] DeciSigma1.Constraints.signedDual_signedVar
attribute [local simp] DeciSigma1.Constraints.signedVar_base_sign
attribute [local simp] DeciSigma1.Constraints.upperAt_nil_iff
attribute [local simp] DeciSigma1.Full.Closure.configSet_assignmentOf
attribute [local simp] DeciSigma1.Full.Closure.flipEmb_apply
attribute [local simp] DeciSigma1.Full.Closure.mem_factList
attribute [local simp] DeciSigma1.Full.Closure.mem_negList
attribute [local simp] DeciSigma1.Full.Models.GroundBound.holds_map
attribute [local simp] DeciSigma1.Full.Models.PrefixPair.nonBottomPrefixes_realize
attribute [local simp] DeciSigma1.Full.Models.Signed.FinitePinning.symmetrize_toTree
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Logic.ConjunctiveClause.holds_append
attribute [local simp] DeciSigma1.Satisfiability.SignSelection.selectedShape_domain
attribute [local simp] DeciSigma1.Satisfiability.leastShape_fn_nil
attribute [local simp] DeciSigma1.Semantics.FTree.height_bot
attribute [local simp] DeciSigma1.Semantics.FTree.height_top
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_dual
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_normalize
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
attribute [local simp] DeciSigma1.Semantics.FiniteMedian.extendedLabel_toTree_nil
attribute [local simp] DeciSigma1.Semantics.FiniteMedian.median_toTree
attribute [local simp] DeciSigma1.Semantics.PrefixSet.positions_toTree
attribute [local simp] DeciSigma1.Semantics.PrefixSet.toTree_bot
attribute [local simp] DeciSigma1.Semantics.PrefixSet.toTree_eq_bot_iff
attribute [local simp] DeciSigma1.Semantics.PrefixSet.toTree_le_toTree
attribute [local simp] DeciSigma1.Semantics.SignSelection.mix_fn
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.descend_bot
attribute [local simp] DeciSigma1.Semantics.Tree.descend_node
attribute [local simp] DeciSigma1.Semantics.Tree.descend_top
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_bot
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_nil
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_top
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_top
attribute [local simp] DeciSigma1.Semantics.Tree.node_le_node_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff
attribute [local simp] DeciSigma1.Semantics.Tree.trace_bot
attribute [local simp] DeciSigma1.Semantics.Tree.trace_cons
attribute [local simp] DeciSigma1.Semantics.Tree.trace_nil
attribute [local simp] DeciSigma1.Semantics.Tree.trace_top
attribute [local simp] DeciSigma1.Semantics.bot_treeLe
attribute [local simp] DeciSigma1.Semantics.dual_bot
attribute [local simp] DeciSigma1.Semantics.dual_fn
attribute [local simp] DeciSigma1.Semantics.dual_involutive
attribute [local simp] DeciSigma1.Semantics.dual_le_iff
attribute [local simp] DeciSigma1.Semantics.dual_node
attribute [local simp] DeciSigma1.Semantics.dual_top
attribute [local simp] DeciSigma1.Semantics.fullTree_fn
attribute [local simp] DeciSigma1.Semantics.node_treeLe_node_iff
attribute [local simp] DeciSigma1.Semantics.normalize_bot
attribute [local simp] DeciSigma1.Semantics.normalize_false_variance
attribute [local simp] DeciSigma1.Semantics.normalize_fn
attribute [local simp] DeciSigma1.Semantics.normalize_involutive
attribute [local simp] DeciSigma1.Semantics.normalize_node
attribute [local simp] DeciSigma1.Semantics.normalize_top
attribute [local simp] DeciSigma1.Semantics.normalize_true
attribute [local simp] DeciSigma1.Semantics.top_treeLe_iff
attribute [local simp] DeciSigma1.Semantics.treeLe_bot_iff
attribute [local simp] DeciSigma1.Semantics.treeLe_false_iff_le
attribute [local simp] DeciSigma1.Semantics.treeLe_top
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open Arithmetic
namespace DeciSigma1
theorem _root_.solution (σ k N : ℕ) :
    smallHoleBound σ k N ≤ (fun x : ℕ => 2 ^ x)^[4]
      ((k + N + 20) ^ (2 * k + 6)) := by
  let p := (k + N + 20) ^ (2 * k + 5)
  let L := Holes.Tail.tailLengthBound σ k N
  have ht : L ≤ exp2^[2] p := Holes.Tail.tailLengthBound_le_double_exp2 σ k N
  have h₁ : N + L + 1 ≤ exp2^[2] (N + p + 2) := by
    calc
      N + L + 1 ≤ exp2^[2] (N + p + 1) + exp2^[2] 0 :=
        Nat.add_le_add ((Nat.add_le_add (le_iterate_exp2 2 N) ht).trans
          (iterate_exp2_add_le 2 N p (by omega))) (by decide)
      _ ≤ exp2^[2] (N + p + 2) := by
        simpa using iterate_exp2_add_le 2 (N + p + 1) 0 (by omega)
  have h₂ : k * (N + L + 1) ≤ exp2^[2] (k + (N + p + 2) + 1) :=
    (Nat.mul_le_mul (le_iterate_exp2 2 k) h₁).trans
      (iterate_exp2_mul_le 2 k (N + p + 2) (by omega))
  have h₃ : k + (k * (N + L + 1) + 1) + 16 ≤
      exp2^[2] (2 * k + N + p + 21) := by
    calc
      _ = (k + k * (N + L + 1)) + 17 := by omega
      _ ≤ exp2^[2] (k + (k + (N + p + 2) + 1) + 1) + exp2^[2] 16 :=
        Nat.add_le_add ((Nat.add_le_add (le_iterate_exp2 2 k) h₂).trans
          (iterate_exp2_add_le 2 k _ (by omega)))
          ((succ_le_exp2 16).trans (le_exp2 _))
      _ ≤ exp2^[2] (2 * k + N + p + 21) := by
        convert iterate_exp2_add_le 2 (k + (k + (N + p + 2) + 1) + 1) 16 (by omega)
          using 1
        congr 1
        omega
  have harg : 2 * k + N + p + 25 ≤ (k + N + 20) ^ (2 * k + 6) := by
    let R := k + N + 20
    have hR : 20 ≤ R := by dsimp [R]; omega
    have hp : R ≤ p := by
      have h : R ^ 1 ≤ R ^ (2 * k + 5) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa only [pow_one] using h
    have hlin : 2 * k + N + 25 ≤ 2 * R := by dsimp [R]; omega
    calc
      _ ≤ 3 * p := by omega
      _ ≤ R * p := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by
        dsimp [R, p]
        rw [show 2 * k + 6 = (2 * k + 5) + 1 by omega, pow_succ]
        ring
  calc
    smallHoleBound σ k N = Holes.Fresh.freshTupleBound k (k * (N + L + 1) + 1) := rfl
    _ ≤ exp2 (exp2 ((k + (k * (N + L + 1) + 1) + 16) ^ 4)) :=
      Holes.Fresh.freshTupleBound_le_double_exp2 _ _
    _ ≤ exp2 (exp2 ((exp2^[2] (2 * k + N + p + 21)) ^ 4)) :=
      exp2_mono (exp2_mono (Nat.pow_le_pow_left h₃ 4))
    _ ≤ exp2^[4] (2 * k + N + p + 25) :=
      exp2_mono (exp2_mono (double_exp2_pow_le _ 4))
    _ ≤ _ := iterate_exp2_mono 4 harg
end DeciSigma1
