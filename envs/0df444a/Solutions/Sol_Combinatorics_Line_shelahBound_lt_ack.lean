-- Prove2me | solution 1 for Combinatorics.Line.shelahBound_lt_ack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:36.967646+00:00
-- url     : https://prove2.me/submissions/e06550b8-a24d-4f06-915e-0208b5768705

module
public import Mathlib.Computability.Ackermann
public import Definitions.Def_ShelahHalesJewett_HalesJewett
public import Definitions.Def_ShelahHalesJewett_Ackermann
public import Theorems.Thm_Combinatorics_Subspace_insensitiveBound_le_ack
section
@[expose] public section
namespace Combinatorics
namespace Subspace
end Subspace
namespace Line
private lemma shelahBound_succ_le_ack (j r : ℕ) : shelahBound (j + 1) r ≤ ack 5 (2 * j + r) := by
  induction j with
  | zero => grind [shelahBound, ack_pos 5 r]
  | succ j ih =>
    rw [shelahBound, (by grind : 2 * (j + 1) + r = 2 * j + r + 1 + 1), ack_succ_succ,
      ack_succ_succ]
    apply (Subspace.insensitiveBound_le_ack _ _ _).trans
    apply ack_mono_right 4
    grind [add_lt_ack 5 (2 * j + r), ack_three (ack 5 (2 * j + r)),
      Nat.lt_two_pow_self (n := ack 5 (2 * j + r)),
      ack_le_ack (by grind : 3 ≤ 4) (le_refl (ack 5 (2 * j + r)))]
variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]
end Line
end Combinatorics
end
end

set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
open Combinatorics.Line
namespace Combinatorics.Line
theorem _root_.solution (k r : ℕ) : shelahBound k r < ack 5 (2 * k + r) := by
  rcases k with _ | j
  · grind [shelahBound, one_lt_ack_succ_left 4 r]
  · exact (shelahBound_succ_le_ack j r).trans_lt (ack_strictMono_right 5 (by grind))
end Combinatorics.Line
