-- Prove2me | solution 1 for DeciSigma1.Constraints.GroundCompiler.extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:04:18.115784+00:00
-- url     : https://prove2.me/submissions/945569ab-2eb2-42bd-872e-3815c71d05bc

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Option
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_GroundBounds
public import Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_isRankedLiteral_compile
public import Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_extend_original
public import Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_extend_fresh
public import Theorems.Thm_DeciSigma1_Automata_lowerRun_nil
public import Theorems.Thm_DeciSigma1_Automata_lowerRun_snoc
public import Theorems.Thm_DeciSigma1_Automata_mem_down
public import Theorems.Thm_DeciSigma1_Automata_mem_lowerStep
public import Theorems.Thm_DeciSigma1_Automata_mem_up
public import Theorems.Thm_DeciSigma1_Automata_mem_upperStep
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Automata_upperRun_snoc
public import Theorems.Thm_DeciSigma1_Automata_upperStep_empty
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_map
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
public import Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_selectedShape_domain
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_fn_nil
public import Theorems.Thm_DeciSigma1_Semantics_FTree_height_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_height_top
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
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
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.lowerRun_nil
attribute [local simp] DeciSigma1.Automata.lowerRun_snoc
attribute [local simp] DeciSigma1.Automata.mem_down
attribute [local simp] DeciSigma1.Automata.mem_lowerStep
attribute [local simp] DeciSigma1.Automata.mem_up
attribute [local simp] DeciSigma1.Automata.mem_upperStep
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Automata.upperRun_snoc
attribute [local simp] DeciSigma1.Automata.upperStep_empty
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
attribute [local simp] DeciSigma1.Satisfiability.SignSelection.selectedShape_domain
attribute [local simp] DeciSigma1.Satisfiability.leastShape_fn_nil
attribute [local simp] DeciSigma1.Semantics.FTree.height_bot
attribute [local simp] DeciSigma1.Semantics.FTree.height_top
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_dual
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_normalize
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
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
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Constraints.GroundCompiler.extend_original
attribute [local simp] DeciSigma1.Constraints.GroundCompiler.extend_fresh

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints DeciSigma1.Constraints.GroundCompiler
open DeciSigma1.Semantics
variable {n k : ℕ} {V : Type*}
namespace DeciSigma1.Constraints.GroundCompiler
theorem _root_.solution (lower : Bool) (g : FTree n) (x : Fin k) (Γ : List (LitT n (Fin k))) :
    Ranked.Extension Γ (lift Γ _ ++ compile lower (Fin.castAdd _ x) g (occurrenceVar g))
      (fun z => lower = true ∧ k ≤ z.val) (fun z => lower = false ∧ k ≤ z.val) (rank g) := by
  let Fresh : Fin (k + Fintype.card (Occurrence g)) → Prop := fun z => k ≤ z.val
  have hf (o : Occurrence g) : Fresh (occurrenceVar g o) := by simp [Fresh, occurrenceVar]
  have hr (o : Occurrence g) : rank (k := k) g (occurrenceVar g o) = rank g (Fin.castAdd _ x) +
      depth g o := by
    simp [rank, occurrenceVar]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; omega
  · intro z hz; omega
  · intro z hz ht; simp_all
  · intro z
    by_cases hz : z.val < k
    · exact Or.inl ⟨⟨z.val, hz⟩, rfl⟩
    · cases lower <;> simp_all
  · intro l hl
    exact List.mem_append_left _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
  · intro a b hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨l, hl, he⟩ := List.mem_map.mp hz
      cases l <;> simp only [LitT.map, LitT.le.injEq, reduceCtorEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, hl, rfl, rfl⟩
    · exact False.elim (isRankedLiteral_compile lower g _ _ Fresh (rank g) hf hr _ hz)
  · intro a z hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨l, hl, he⟩ := List.mem_map.mp hz
      cases l <;> simp only [LitT.map, LitT.fLe.injEq, reduceCtorEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inl ⟨_, _, hl, rfl, rfl⟩
    · obtain ⟨hd, ha⟩ := isRankedLiteral_compile lower g _ _ Fresh (rank g) hf hr _ hz
      exact Or.inr ⟨fun i => ⟨⟨hd, (ha i).1⟩, (ha i).2⟩, by simp [hd]⟩
  · intro z a hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨l, hl, he⟩ := List.mem_map.mp hz
      cases l <;> simp only [LitT.map, LitT.leF.injEq, reduceCtorEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inl ⟨_, _, hl, rfl, rfl⟩
    · obtain ⟨hd, ha⟩ := isRankedLiteral_compile lower g _ _ Fresh (rank g) hf hr _ hz
      exact Or.inr ⟨fun i => ⟨⟨hd, (ha i).1⟩, (ha i).2⟩, by simp [hd]⟩
end DeciSigma1.Constraints.GroundCompiler
