-- Prove2me | solution 1 for DeciSigma1.Full.Models.mem_nonBottomPrefixes_of_hasTopPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:34:01.354128+00:00
-- url     : https://prove2.me/submissions/360b8b35-dd82-41e1-916a-ef6cec5aa13e

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_eq_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_eq_top_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}
namespace DeciSigma1.Full.Models
theorem _root_.solution (t : Semantics.Tree n) (w : List (Fin n)) :
    HasTopPrefix t w → w ∈ (nonBottomPrefixes t).carrier := by
  intro ha hc
  have ht := (Semantics.Tree.trace_eq_top_iff _ _).mpr ha
  have hb := (Semantics.Tree.trace_eq_bot_iff _ _).mpr hc
  exact Tree.bot_ne_top (hb.symm.trans ht)
end DeciSigma1.Full.Models
