-- Prove2me | solution 1 for DeciSigma1.Full.Models.le_dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:34:51.809506+00:00
-- url     : https://prove2.me/submissions/8b57b58f-89ff-41c7-9ac2-254f3de62519

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_dual_involutive
public import Theorems.Thm_DeciSigma1_Semantics_dual_le_iff
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_dual
attribute [local simp] DeciSigma1.Semantics.dual_involutive
attribute [local simp] DeciSigma1.Semantics.dual_le_iff



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}
namespace DeciSigma1.Full.Models
theorem _root_.solution (t : Semantics.Tree n) (g : FTree n) :
    t ≤ g.dual.toTree ↔ g.toTree ≤ Tree.dual t := by
  rw [FTree.toTree_dual, ← dual_le_iff, dual_involutive]
end DeciSigma1.Full.Models
