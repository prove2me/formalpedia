-- Prove2me | solution 1 for Champernowne.champernowne_normal_ten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:44.767799+00:00
-- url     : https://prove2.me/submissions/30b97c4b-5d8c-4465-ae33-e04bc5b707b6

module
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Definitions.Def_LeanPool_Champernowne_Main
public import Theorems.Thm_Champernowne_champernowne_normal

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution : IsNormalSequence 10 (champDigit 10) :=
  champernowne_normal 10 (by norm_num)
end Champernowne
