-- Prove2me | solution 1 for Combinatorics.Line.exists_mono_of_ack_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:48.618797+00:00
-- url     : https://prove2.me/submissions/e7d7e483-7852-44a7-b50e-844ea51462bf

module
public import Mathlib.Computability.Ackermann
public import Definitions.Def_ShelahHalesJewett_HalesJewett
public import Definitions.Def_ShelahHalesJewett_Ackermann
public import Theorems.Thm_Combinatorics_Line_shelahBound_lt_ack
public import Theorems.Thm_Combinatorics_Line_exists_mono_of_shelahBound_le


set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
open Combinatorics.Line
variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]
namespace Combinatorics.Line
theorem _root_.solution [Nonempty α]
    (h : ack 5 (2 * Fintype.card α + Fintype.card κ) ≤ Fintype.card ι) (C : (ι → α) → κ) :
    ∃ l : Line α ι, l.IsMono C :=
  exists_mono_of_shelahBound_le ((shelahBound_lt_ack _ _).le.trans h) C
end Combinatorics.Line
