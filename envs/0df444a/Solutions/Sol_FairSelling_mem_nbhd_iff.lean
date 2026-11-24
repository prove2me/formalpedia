-- Prove2me | solution 1 for FairSelling.mem_nbhd_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:07:37.823642+00:00
-- url     : https://prove2.me/submissions/cf8d23d0-d642-4826-b613-93dccdae640e

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsMatching

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
omit [DecidableEq α] [DecidableEq β]
namespace FairSelling
theorem _root_.solution {B : Finset β} {acc : α → β → Prop} [DecidableRel acc] {a : α} {b : β} :
    b ∈ nbhd B acc a ↔ b ∈ B ∧ acc a b := by
  simp [nbhd]
end FairSelling
