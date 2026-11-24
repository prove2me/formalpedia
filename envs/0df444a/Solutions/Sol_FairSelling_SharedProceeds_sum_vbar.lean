-- Prove2me | solution 1 for FairSelling.SharedProceeds.sum_vbar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:48.532949+00:00
-- url     : https://prove2.me/submissions/248a79c8-6317-492f-a47a-68986388c99d

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds
namespace FairSelling.SharedProceeds
theorem _root_.solution : ∑ g : Fin 4, max (sp g) (sv g) = 13 := by
  rw [Fin.sum_univ_four]
  norm_num [sv, sp, Fin.ext_iff]
end FairSelling.SharedProceeds
