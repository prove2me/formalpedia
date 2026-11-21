-- Prove2me | solution 1 for Champernowne.champPrefix_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:38:27.922923+00:00
-- url     : https://prove2.me/submissions/2df29b72-edcb-4964-99ce-9cad1e6698aa

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b n : ℕ) : champPrefix b n <+: champBlocks b n :=
  List.take_prefix n _
end Champernowne
