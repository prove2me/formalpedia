-- Prove2me | solution 1 for Comp.lfp_eq_coe_fixFrom_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:32:26.614156+00:00
-- url     : https://prove2.me/submissions/47672413-9ce7-4c0e-9035-f9d2d0c4fa1a

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
import Theorems.Thm_Comp_mono_of_coe
import Theorems.Thm_Comp_coe_empty_le_lfp
import Theorems.Thm_Comp_lfp_eq_coe_fixFrom
import Theorems.Thm_Comp_fixFrom_empty_fixed

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
namespace Comp
theorem _root_.solution (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) :
    F.lfp = (↑(fixFrom f ∅) : Set S) :=
  lfp_eq_coe_fixFrom F f hf ∅ (coe_empty_le_lfp F) (fixFrom_empty_fixed f (mono_of_coe F f hf))
end Comp
