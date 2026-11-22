-- Prove2me | solution 1 for DeciSigma1.Constraints.upperAt_iff_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:36:54.184375+00:00
-- url     : https://prove2.me/submissions/15bea793-cfca-4107-8c25-d69a35749952

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Theorems.Thm_DeciSigma1_Automata_mem_up
public import Theorems.Thm_DeciSigma1_Automata_mem_down
public import Theorems.Thm_DeciSigma1_Automata_mem_upperStep
public import Theorems.Thm_DeciSigma1_Automata_mem_lowerStep
public import Theorems.Thm_DeciSigma1_Automata_lowerRun_nil
public import Theorems.Thm_DeciSigma1_Automata_upperRun_snoc
public import Theorems.Thm_DeciSigma1_Automata_lowerRun_snoc
public import Theorems.Thm_DeciSigma1_Automata_upperStep_empty
public import Theorems.Thm_DeciSigma1_Automata_upperRun_closed
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Constraints_LowerAt_comp
public import Theorems.Thm_DeciSigma1_Constraints_LowerAt_factor
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_comp
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_factor
public import Theorems.Thm_DeciSigma1_Constraints_holdsT_map
public import Theorems.Thm_DeciSigma1_Constraints_holds_false
public import Theorems.Thm_DeciSigma1_Constraints_lowerAt_nil_iff
public import Theorems.Thm_DeciSigma1_Constraints_mem_derivedPairs
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Constraints_upperAt_nil_iff
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
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
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Constraints.holdsT_map
attribute [local simp] DeciSigma1.Constraints.holds_false
attribute [local simp] DeciSigma1.Constraints.lowerAt_nil_iff
attribute [local simp] DeciSigma1.Constraints.sat_false
attribute [local simp] DeciSigma1.Constraints.upperAt_nil_iff
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_dual
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_normalize
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
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


attribute [local simp] DeciSigma1.Automata.mem_up
attribute [local simp] DeciSigma1.Automata.mem_down
attribute [local simp] DeciSigma1.Automata.mem_upperStep
attribute [local simp] DeciSigma1.Automata.mem_lowerStep
attribute [local simp] DeciSigma1.Automata.lowerRun_nil
attribute [local simp] DeciSigma1.Automata.upperRun_snoc
attribute [local simp] DeciSigma1.Automata.lowerRun_snoc
attribute [local simp] DeciSigma1.Automata.upperStep_empty

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
namespace DeciSigma1.Constraints
theorem _root_.solution (Γ : List (LitT n V)) (π : List (Fin n)) (x y : V) :
    UpperAt Γ π x y ↔ y ∈ Automata.upperRun Γ x π := by
  induction π using List.reverseRecOn generalizing y with
  | nil => simp [Automata.upperRun, Automata.upper, Automata.Semiautomaton.run,
      runFrom, Automata.mem_up, mem_derivedPairs]
  | append_singleton π i ih =>
    rw [Automata.upperRun_snoc, Automata.mem_upperStep]
    constructor
    · intro h
      obtain ⟨r, hp, ht⟩ := h.factor
      cases ht with
      | cons hd hl ht =>
        exact ⟨_, Automata.upperRun_closed ((ih _).mp hp) ((mem_derivedPairs Γ _ _).mpr hd),
          _, hl, (mem_derivedPairs Γ _ _).mpr (upperAt_nil_iff.mp ht)⟩
    · rintro ⟨r, hr, a, hl, hd⟩
      have ht : UpperAt Γ [i] r y :=
        .cons (.refl _) hl (.nil ((mem_derivedPairs Γ _ _).mp hd))
      exact ((ih _).mpr hr).comp ht
end DeciSigma1.Constraints
