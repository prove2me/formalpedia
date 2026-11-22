-- Prove2me | solution 1 for Comp.gfp_eq_coe_fixFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:27:28.415467+00:00
-- url     : https://prove2.me/submissions/d7cbcccf-74f1-4bcc-90a1-0cd7a0aea57d

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
import Theorems.Thm_Comp_gfp_le_coe_fixAux
import Theorems.Thm_OrderHom_eq_gfp_of_fixed_of_ge


set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
namespace Comp
theorem _root_.solution (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (x : Finset S)
    (hx : F.gfp ≤ (↑x : Set S)) (hfix : f (fixFrom f x) = fixFrom f x) :
    F.gfp = (↑(fixFrom f x) : Set S) := by
  have hge : F.gfp ≤ (↑(fixFrom f x) : Set S) := gfp_le_coe_fixAux F f hf _ x hx
  have hfixS : F (↑(fixFrom f x) : Set S) = (↑(fixFrom f x) : Set S) := by
    rw [← hf, hfix]
  exact (OrderHom.eq_gfp_of_fixed_of_ge F hfixS hge).symm
end Comp
