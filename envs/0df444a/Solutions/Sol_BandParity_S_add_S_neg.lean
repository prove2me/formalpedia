-- Prove2me | solution 1 for BandParity.S_add_S_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:43.676195+00:00
-- url     : https://prove2.me/submissions/6d7305d2-e79f-4408-bf75-5f4ff98a196d

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_p_mul_S
public import Theorems.Thm_BandParity_card_class
public import Theorems.Thm_BandParity_cosetSum_add_cosetSum_neg
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_quartic_apply_neg_one
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
theorem _root_.solution (hp8 : p % 8 = 5) (hp5 : 5 < p) (z : GaussianInt)
    (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    S χ z + S χ (-z) = ((p - 1) / 4 : ℕ) := by
  have hodd := quartic_apply_neg_one χ hχ hp8
  have hz0 : z ≠ 0 := by rcases hz with rfl | rfl | rfl | rfl <;> decide
  have hnz : -z = 1 ∨ -z = gi ∨ -z = -1 ∨ -z = -gi := by
    rcases hz with rfl | rfl | rfl | rfl <;> simp
  have e := cosetSum_add_cosetSum_neg hodd z hz0
  have hc := card_class hχ z hz
  rw [← p_mul_S hχ hp5, ← p_mul_S hχ hp5, ← mul_add] at e
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have := mul_left_cancel₀ hp0 e
  rw [this]; congr 1; omega
end BandParity
