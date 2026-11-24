-- Prove2me | solution 2 for FairSelling.FeigeNorkin.fnR_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:51:49.537508+00:00
-- url     : https://prove2.me/submissions/68a7bd7a-d63b-4958-96c7-7aee453d61ae

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin
namespace FairSelling.FeigeNorkin
theorem _root_.solution :
    (∑ j ∈ ({2, 3, 4} : Finset (Fin 8)), fnR j) = 36 ∧
    (∑ j ∈ ({0, 1} : Finset (Fin 8)), fnR j) = 36 ∧
    (∑ j ∈ ({5, 6, 7} : Finset (Fin 8)), fnR j) = 36 := by
  refine ⟨by decide, by decide, by decide⟩
end FairSelling.FeigeNorkin
