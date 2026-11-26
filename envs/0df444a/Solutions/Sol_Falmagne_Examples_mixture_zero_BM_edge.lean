-- Prove2me | solution 1 for Falmagne.Examples.mixture_zero_BM_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:10.301667+00:00
-- url     : https://prove2.me/submissions/170790c2-6864-49bf-ba95-fa34a54feac3

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_mixture_full_menu_middle_probability_zero
public import Theorems.Thm_Falmagne_blockMarschak_univ


set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution : blockMarschak mixtureChoice (1 : Fin 4) univ = 0 := by
  rw [blockMarschak_univ]
  exact mixture_full_menu_middle_probability_zero
end Falmagne.Examples
