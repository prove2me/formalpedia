-- Prove2me | solution 1 for Comp.gfp_eq_coe_fixFrom_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:32:16.814976+00:00
-- url     : https://prove2.me/submissions/007206b0-43ea-4845-ab7b-eaeb387f5dbd

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
import Theorems.Thm_Comp_mono_of_coe
import Theorems.Thm_Comp_gfp_le_coe_univ
import Theorems.Thm_Comp_gfp_eq_coe_fixFrom
import Theorems.Thm_Comp_fixFrom_univ_fixed

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
namespace Comp
theorem _root_.solution (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) :
    F.gfp = (↑(fixFrom f Finset.univ) : Set S) :=
  gfp_eq_coe_fixFrom F f hf Finset.univ (gfp_le_coe_univ F)
    (fixFrom_univ_fixed f (mono_of_coe F f hf))
end Comp
