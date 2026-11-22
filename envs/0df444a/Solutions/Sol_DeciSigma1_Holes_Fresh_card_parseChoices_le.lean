-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.card_parseChoices_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:23.978706+00:00
-- url     : https://prove2.me/submissions/4e843646-f813-453c-90bd-07c584efab7b

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_prefixOccurrenceCuts_le


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (hfr : ∀ i, T.Fresh W i) (t : ℕ) (z : List α) :
    (parseChoices W t z).card ≤ 2 ^ (k * (Fintype.card S - 1)) := by
  calc
    _ ≤ ((prefixOccurrenceCuts W z).powerset).card := card_image_le
    _ = 2 ^ (prefixOccurrenceCuts W z).card := card_powerset _
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (card_prefixOccurrenceCuts_le hfr z)
end DeciSigma1.Holes.Fresh
