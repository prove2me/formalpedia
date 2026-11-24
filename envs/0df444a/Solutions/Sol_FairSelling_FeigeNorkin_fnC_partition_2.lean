-- Prove2me | solution 2 for FairSelling.FeigeNorkin.fnC_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:51:59.730124+00:00
-- url     : https://prove2.me/submissions/7dd5f414-699b-4d87-aca6-a93719e2111d

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin
namespace FairSelling.FeigeNorkin
theorem _root_.solution :
    (∑ j ∈ ({2, 5} : Finset (Fin 8)), fnC j) = 36 ∧
    (∑ j ∈ ({0, 3, 6} : Finset (Fin 8)), fnC j) = 36 ∧
    (∑ j ∈ ({1, 4, 7} : Finset (Fin 8)), fnC j) = 36 := by
  refine ⟨by decide, by decide, by decide⟩
end FairSelling.FeigeNorkin
