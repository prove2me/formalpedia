-- Prove2me | solution 1 for Comp.lfp_eq_coe_fixFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:27:42.448798+00:00
-- url     : https://prove2.me/submissions/135daba5-2cfb-4a1b-a549-90bf6e1521e6

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
import Theorems.Thm_Comp_coe_fixAux_le_lfp
import Theorems.Thm_OrderHom_eq_lfp_of_fixed_of_le


set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
namespace Comp
theorem _root_.solution (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (x : Finset S)
    (hx : (↑x : Set S) ≤ F.lfp) (hfix : f (fixFrom f x) = fixFrom f x) :
    F.lfp = (↑(fixFrom f x) : Set S) := by
  have hle : (↑(fixFrom f x) : Set S) ≤ F.lfp := coe_fixAux_le_lfp F f hf _ x hx
  have hfixS : F (↑(fixFrom f x) : Set S) = (↑(fixFrom f x) : Set S) := by
    rw [← hf, hfix]
  exact (OrderHom.eq_lfp_of_fixed_of_le F hfixS hle).symm
end Comp
