-- Prove2me | solution 1 for DeciSigma1.Full.Closure.dead_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:35.756508+00:00
-- url     : https://prove2.me/submissions/38449bf1-123c-459e-8f0b-99dc6bf63116

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Closure_configSet_assignmentOf
public import Theorems.Thm_DeciSigma1_Full_Closure_Reach_mem_of_closed
public import Theorems.Thm_DeciSigma1_Full_Closure_reach_extend
public import Theorems.Thm_DeciSigma1_Full_Closure_mem_leastClosure
public import Theorems.Thm_DeciSigma1_Full_Closure_mem_seedClosure
public import Theorems.Thm_DeciSigma1_Full_Closure_leastClosure_subset
public import Theorems.Thm_DeciSigma1_Full_Closure_live_iff
public import Theorems.Thm_DeciSigma1_Full_Closure_collision_return
public import Theorems.Thm_DeciSigma1_Full_Closure_Consistent_not_flip
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Constraints_holdsT_map
public import Theorems.Thm_DeciSigma1_Constraints_holds_false
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Full_Models_GroundBound_holds_map
public import Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_nonBottomPrefixes_realize
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
attribute [local simp] DeciSigma1.Constraints.sat_false
attribute [local simp] DeciSigma1.Full.Models.GroundBound.holds_map
attribute [local simp] DeciSigma1.Full.Models.PrefixPair.nonBottomPrefixes_realize
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


attribute [local simp] DeciSigma1.Full.Closure.configSet_assignmentOf

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution (hsat : Avoids Γ (leastClosure c Γ) ∧ Consistent (leastClosure c Γ))
    {p : V} {s : Bool} {u : List (Fin n)} :
    ¬ Live c Γ (p, s, u) ↔
      (∃ n, Neg Γ n ∧ Reach c Γ (p, s, u) n) ∨
      (∃ δ, (p, !s, u ++ δ) ∈ leastClosure c Γ) ∨
      (∃ δ, Reach c Γ (p, s, u) (p, !s, u ++ δ)) := by
  classical
  constructor
  · intro hdead
    by_cases hn : Avoids Γ (seedClosure c Γ (p, s, u))
    · have hd : ¬ Consistent (seedClosure c Γ (p, s, u)) :=
        fun hd => hdead (live_iff.mpr ⟨hn, hd⟩)
      simp only [Consistent, not_forall] at hd
      obtain ⟨a, b, hab, ha, hb, _⟩ := hd
      cases hab with
      | pair v w =>
        rcases mem_seedClosure.mp ha with hma | hra <;> rcases mem_seedClosure.mp hb with hmb | hrb
        · exact (hsat.2 (.pair v w) hma hmb).elim
        · obtain ⟨f, hf, hfa⟩ := mem_leastClosure.mp hma
          obtain ⟨δ, hδ⟩ := collision_return hfa hrb
          exact Or.inr (Or.inl ⟨δ, mem_leastClosure.mpr ⟨f, hf, hδ⟩⟩)
        · obtain ⟨f, hf, hfb⟩ := mem_leastClosure.mp hmb
          obtain ⟨δ, hδ⟩ := collision_return hfb hra
          exact Or.inr (Or.inl ⟨δ, mem_leastClosure.mpr ⟨f, hf, hδ⟩⟩)
        · exact Or.inr (Or.inr (collision_return hra hrb))
    · simp only [Avoids, not_forall, not_not] at hn
      obtain ⟨n, hnc, hneg⟩ := hn
      rcases mem_seedClosure.mp hnc with hm | hr
      · exact (hsat.1 hm hneg).elim
      · exact Or.inl ⟨n, hneg, hr⟩
  · intro h hlive
    obtain ⟨S, hS, ha⟩ := hlive
    rcases h with ⟨n, hn, hr⟩ | ⟨δ, hm⟩ | ⟨δ, hr⟩
    · exact hS.avoids (hr.mem_of_closed hS.closed ha) hn
    · exact hS.consistent.not_flip
        ((reach_extend p s u δ).mem_of_closed hS.closed ha) (leastClosure_subset hS hm)
    · exact hS.consistent.not_flip
        ((reach_extend p s u δ).mem_of_closed hS.closed ha)
        (hr.mem_of_closed hS.closed ha)
end DeciSigma1.Full.Closure
