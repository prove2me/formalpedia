-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.le_iff_positions_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:04:18.589368+00:00
-- url     : https://prove2.me/submissions/da8f5968-eb30-4e09-969b-2a2599264ab5

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Theorems.Thm_DeciSigma1_Semantics_Tree_positions_le_of_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_of_positions_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution {t u : Tree n} (ht : t.IsTopFree) (hu : u.IsTopFree) :
    t ≤ u ↔ t.positions ≤ u.positions :=
  ⟨positions_le_of_le hu, le_of_positions_le ht⟩
end DeciSigma1.Semantics.Tree
