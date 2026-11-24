-- Prove2me | solution 1 for FairSelling.nbhd_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:07:35.162078+00:00
-- url     : https://prove2.me/submissions/bda20056-2a20-42e5-998d-dcd8add03c4a

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsMatching

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
omit [DecidableEq α] [DecidableEq β]
namespace FairSelling
theorem _root_.solution (B : Finset β) (acc : α → β → Prop) [DecidableRel acc] (a : α) :
    nbhd B acc a ⊆ B := Finset.filter_subset _ _
end FairSelling
