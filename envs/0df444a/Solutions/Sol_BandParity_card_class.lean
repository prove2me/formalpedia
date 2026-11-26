-- Prove2me | solution 1 for BandParity.card_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:57:33.727209+00:00
-- url     : https://prove2.me/submissions/e1192925-b55c-4290-b249-ff06b5813616

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_apply_eq_zero_iff
public import Theorems.Thm_BandParity_card_class_eq
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_quartic_values
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (z : GaussianInt) (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    4 * (univ.filter (fun n : ZMod p => χ n = z)).card = p - 1 := by
  rw [card_class_eq hχ z hz]
  have hpart : ∀ n : ZMod p, (1 : ℕ) = (if χ n = 0 then 1 else 0) + (if χ n = 1 then 1 else 0) +
      (if χ n = gi then 1 else 0) + (if χ n = -1 then 1 else 0) + (if χ n = -gi then 1 else 0) := by
    intro n
    by_cases hn : n = 0
    · rw [hn, MulChar.map_zero]; decide
    · rcases quartic_values χ hχ hn with h | h | h | h <;> rw [h] <;> decide
  have htot : (Fintype.card (ZMod p) : ℕ) = ∑ n : ZMod p, (1 : ℕ) := by simp
  rw [Finset.sum_congr rfl (fun n _ => hpart n)] at htot
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at htot
  rw [ZMod.card] at htot
  have h0 : (univ.filter (fun n : ZMod p => χ n = 0)).card = 1 := by
    rw [Finset.card_eq_one]; refine ⟨0, ?_⟩
    ext n; simp [apply_eq_zero_iff hχ]
  rw [h0, card_class_eq hχ gi (by simp), card_class_eq hχ (-1) (by simp),
    card_class_eq hχ (-gi) (by simp)] at htot
  omega
end BandParity
