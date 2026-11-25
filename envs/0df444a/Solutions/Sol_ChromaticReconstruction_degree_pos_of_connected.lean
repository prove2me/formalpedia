-- Prove2me | solution 1 for ChromaticReconstruction.degree_pos_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:30:21.916819+00:00
-- url     : https://prove2.me/submissions/7f7c3f1b-2657-4049-8bcb-c94cae51bd2b

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] {S : SimpleGraph K}
namespace ChromaticReconstruction
theorem _root_.solution (hS : S.Connected) (hk : 2 ≤ Fintype.card K) (x : K) :
    1 ≤ S.degree x := by
  haveI : Nontrivial K := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  exact hS.preconnected.degree_pos_of_nontrivial x
end ChromaticReconstruction
