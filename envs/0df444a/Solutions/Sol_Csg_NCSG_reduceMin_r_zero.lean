-- Prove2me | solution 1 for Csg.NCSG.reduceMin_r_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:51.536263+00:00
-- url     : https://prove2.me/submissions/b418db46-ab7b-4350-901e-672d961b5a68

import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_CoalitionComplement

set_option autoImplicit true
open Csg
open Csg.NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players)
variable (G : NCSG S Players A)
namespace Csg.NCSG
theorem _root_.solution (hrG : ∀ s a, G.r s a = 0) :
    ∀ s a1 a2, (G.reduceMin C).r s a1 a2 = 0 := fun s _ _ => hrG s _
end Csg.NCSG
