-- Prove2me | solution 1 for ConantTerry.Orders.restrict_tree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:21:49.522972+00:00
-- url     : https://prove2.me/submissions/ba936c1b-9928-413c-a1c9-7433cdd42947

import Mathlib
import Definitions.Def_ConantTerry_Orders_function_tree
import Definitions.Def_ConantTerry_Orders_tree_embeddings

section
set_option autoImplicit false
namespace ConantTerry.Dev.RT
open ConantTerry.Orders

theorem node_lt {s t : ℕ} (φ : WordsAtMost s → WordsAtMost t) (hφ : IsProperEmbedding φ)
    (σ : WordsAtMost s) (hσ : σ.val.length < s) : (φ σ).val.length < t := by
  have hl : (σ.val ++ List.replicate (s - σ.val.length) false).length ≤ s := by simp; omega
  have hs : (σ.val ++ List.replicate (s - σ.val.length) false).length = s := by simp; omega
  have hp : σ.val ++ [false] <+: σ.val ++ List.replicate (s - σ.val.length) false := by
    have : s - σ.val.length = (s - σ.val.length - 1) + 1 := by omega
    rw [this, List.replicate_succ]
    exact ⟨List.replicate (s - σ.val.length - 1) false, by simp⟩
  have := hφ.1 σ ⟨_, hl⟩ false hp
  have h2 := hφ.2 ⟨_, hl⟩ hs
  have h3 := this.length_le
  simp only [List.length_append, List.length_singleton] at h3
  omega

end ConantTerry.Dev.RT

namespace ConantTerry.Orders
open ConantTerry.Dev.RT in
theorem chk_restrict_tree {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (δ : ℝ) (hδ : 0 < δ)
    (x : WordsBelow t → X) (y : WordsAt t → Y)
    (r : WordsBelow t → Set.Icc (0 : ℝ) 1)
    (hTree : IsFunctionTree f t δ x y r)
    (φ : WordsAtMost s → WordsAtMost t) (hφ : IsProperEmbedding φ) :
    ∃ (nodes : WordsBelow s → WordsBelow t) (leaves : WordsAt s → WordsAt t),
      (∀ σ, (nodes σ).val = (φ (nodeInclusion σ)).val) ∧
      (∀ η, (leaves η).val = (φ (leafInclusion η)).val) ∧
      IsFunctionTree f s δ (x ∘ nodes) (y ∘ leaves) (r ∘ nodes) := by
  refine ⟨fun σ => ⟨(φ (nodeInclusion σ)).val, node_lt φ hφ _ σ.2⟩,
    fun η => ⟨(φ (leafInclusion η)).val, hφ.2 _ η.2⟩, fun σ => rfl, fun η => rfl, ?_⟩
  intro σ η η' h h'
  have h1 := hφ.1 (nodeInclusion σ) (leafInclusion η) false h
  have h2 := hφ.1 (nodeInclusion σ) (leafInclusion η') true h'
  exact hTree _ _ _ h1 h2

end ConantTerry.Orders
end

theorem solution : type_of% @ConantTerry.Orders.chk_restrict_tree := @ConantTerry.Orders.chk_restrict_tree
