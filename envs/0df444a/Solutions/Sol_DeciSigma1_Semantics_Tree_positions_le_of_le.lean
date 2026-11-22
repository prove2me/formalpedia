-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.positions_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:02:33.226766+00:00
-- url     : https://prove2.me/submissions/f96f57e0-3d65-44bc-a1ed-f6efb14818e2

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
section
@[expose] public section
namespace DeciSigma1.Semantics
variable {n : ℕ}
namespace Tree
private theorem eq_f_of_f_le {b : Sym} (h : Sym.f ≤ b) (hb : b ≠ Sym.top) : b = Sym.f := by
  cases b
  · exact absurd h (by decide)
  · rfl
  · exact absurd rfl hb
end Tree
namespace PrefixSet
end PrefixSet
end DeciSigma1.Semantics
end
end

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution {t u : Tree n} (hu : u.IsTopFree) (h : t ≤ u) :
    t.positions ≤ u.positions := by
  intro π
  induction π using List.reverseRecOn with
  | nil =>
    intro ht
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp u.root_isSome
    exact hb.trans (congrArg some (eq_f_of_f_le (h [] _ b ht hb) fun he => hu [] (he ▸ hb)))
  | append_singleton π i ih =>
    intro ht
    have hπ : u.fn π = some Sym.f := ih (t.positions.prefix_closed π [i] ht)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((u.child_isSome_iff π i).mpr hπ)
    exact hb.trans (congrArg some (eq_f_of_f_le (h _ _ b ht hb) fun he => hu _ (he ▸ hb)))
end DeciSigma1.Semantics.Tree
