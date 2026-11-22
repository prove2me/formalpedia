-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.le_of_positions_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:58:11.903829+00:00
-- url     : https://prove2.me/submissions/fa6c8bc4-a5c6-478b-926d-7466a3c89750

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution {t u : Tree n} (ht : t.IsTopFree) (h : t.positions ≤ u.positions) :
    t ≤ u := by
  intro π a b ha hb
  cases a with
  | bot => exact Sym.bot_le b
  | f => exact (Option.some.inj ((h (show π ∈ t.positions.carrier from ha)).symm.trans hb)).le
  | top => exact absurd ha (ht π)
end DeciSigma1.Semantics.Tree
