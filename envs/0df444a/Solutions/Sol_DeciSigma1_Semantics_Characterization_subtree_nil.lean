-- Prove2me | solution 1 for DeciSigma1.Semantics.Characterization.subtree_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:44.621812+00:00
-- url     : https://prove2.me/submissions/6c81310f-ef31-4ae0-900b-01b97d177347

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Theorems.Thm_DeciSigma1_Semantics_Tree_subtree_fn


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.Characterization
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics.Characterization
theorem _root_.solution (t : Tree n) : t.subtree [] = some t := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
    ((subtree_isSome_iff t []).mpr t.root_isSome)
  rw [hv]
  congr 1
  apply Tree.ext; funext ρ
  rw [subtree_fn hv ρ]; rfl
end DeciSigma1.Semantics.Characterization
