-- Prove2me | solution 1 for DeciSigma1.Full.Closure.sat_iff_isSolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:43:37.268486+00:00
-- url     : https://prove2.me/submissions/30b8dbc2-0f6f-45d2-acc3-e588865c64e6

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Closure_leaf_extension
public import Theorems.Thm_DeciSigma1_Full_Closure_treeLe_iff_leaf
public import Theorems.Thm_DeciSigma1_Full_Closure_configSet_consistent
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



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ}
variable {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution (ρ : V → Semantics.Tree n) :
    SatT c ρ Γ ↔ IsSolution c Γ (configSet c ρ) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, configSet_consistent ρ⟩
    · intro p q hpq hp
      cases hpq with
      | extend v s w i => exact leaf_extension c (ρ v) s w [i] hp
      | move hm =>
        cases hm with
        | copyPlus hl => exact ((treeLe_iff_leaf _ _ _).mp (h _ hl)).1 hp
        | copyMinus hl => exact ((treeLe_iff_leaf _ _ _).mp (h _ hl)).2 hp
        | fLePush i hl =>
          apply ((treeLe_iff_leaf _ _ _).mp (h _ hl)).1
          simpa [configSet] using hp
        | fLePop i hl =>
          have hh := ((treeLe_iff_leaf _ _ _).mp (h _ hl)).2 hp
          simpa [configSet] using hh
        | leFPop i hl =>
          have hh := ((treeLe_iff_leaf _ _ _).mp (h _ hl)).1 hp
          simpa [configSet] using hh
        | leFPush i hl =>
          apply ((treeLe_iff_leaf _ _ _).mp (h _ hl)).2
          simpa [configSet] using hp
    · intro p hp
      cases hp with
      | bot hl => exact (leaf_root_minus c _).mpr (h _ hl)
      | top hl => exact (leaf_root_plus c _).mpr (h _ hl)
    · intro p hp hn
      cases hn with
      | fLe hl =>
          exact leaf_node_nil c _ true (((treeLe_iff_leaf _ _ _).mp (h _ hl)).2 hp)
      | leF hl =>
          exact leaf_node_nil c _ false (((treeLe_iff_leaf _ _ _).mp (h _ hl)).1 hp)
  · intro h l hl
    cases l with
    | le u v =>
      exact (treeLe_iff_leaf _ _ _).mpr
        ⟨fun _ hw => h.closed (.move (.copyPlus hl)) hw,
         fun _ hw => h.closed (.move (.copyMinus hl)) hw⟩
    | fLe a u =>
      apply (treeLe_iff_leaf _ _ _).mpr
      constructor
      · intro w hw
        cases w with
        | nil => exact (leaf_node_nil c _ false hw).elim
        | cons i w =>
          apply h.closed (.move (.fLePush i hl))
          simpa [configSet] using hw
      · intro w hw
        cases w with
        | nil => exact (h.avoids hw (.fLe hl)).elim
        | cons i w =>
          have hh := h.closed (.move (.fLePop i hl)) hw
          simpa [configSet] using hh
    | leF u a =>
      apply (treeLe_iff_leaf _ _ _).mpr
      constructor
      · intro w hw
        cases w with
        | nil => exact (h.avoids hw (.leF hl)).elim
        | cons i w =>
          have hh := h.closed (.move (.leFPop i hl)) hw
          simpa [configSet] using hh
      · intro w hw
        cases w with
        | nil => exact (leaf_node_nil c _ true hw).elim
        | cons i w =>
          apply h.closed (.move (.leFPush i hl))
          simpa [configSet] using hw
    | eqBot u => exact (leaf_root_minus c _).mp (h.facts (.bot hl))
    | eqTop u => exact (leaf_root_plus c _).mp (h.facts (.top hl))
end DeciSigma1.Full.Closure
