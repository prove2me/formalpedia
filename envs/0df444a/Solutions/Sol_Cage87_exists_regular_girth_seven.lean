-- Prove2me | solution 1 for Cage87.exists_regular_girth_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:29:19.431233+00:00
-- url     : https://prove2.me/submissions/378a313c-fd73-47e4-aeff-a18570536b3a

module
public import Definitions.Def_Cage87
public import Definitions.Def_Cage87Solution
public import Theorems.Thm_Cage87_girth_eq
public import Theorems.Thm_Cage87_isRegular


set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution :
    ∃ (G : SimpleGraph (Fin 768)) (_ : DecidableRel G.Adj), G.IsRegularOfDegree 8 ∧ G.girth = 7 :=
  ⟨G, inferInstance, isRegular, girth_eq⟩
end Cage87
