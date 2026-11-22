-- Prove2me | solution 1 for DeciSigma1.Full.Models.mem_nonBottomPrefixes_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:35:19.992745+00:00
-- url     : https://prove2.me/submissions/0dd823e4-40ba-4baf-a580-b70941015100

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Theorems.Thm_DeciSigma1_Full_Models_hasLabel_dual

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}
namespace DeciSigma1.Full.Models
theorem _root_.solution (t : Semantics.Tree n) (w : List (Fin n)) :
    w ∈ (nonBottomPrefixes (Tree.dual t)).carrier ↔ ¬ HasTopPrefix t w := hasLabel_dual t _ |>.not
end DeciSigma1.Full.Models
