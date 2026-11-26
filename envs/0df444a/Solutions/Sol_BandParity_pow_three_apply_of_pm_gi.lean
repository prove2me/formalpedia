-- Prove2me | solution 1 for BandParity.pow_three_apply_of_pm_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:42.391604+00:00
-- url     : https://prove2.me/submissions/cfa54568-eb89-4c8f-88d3-39dbfbc7002c

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_gi_sq
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace BandParity
theorem _root_.solution (χ : MulChar (ZMod p) GaussianInt) {a : ZMod p}
    (h : χ a = gi ∨ χ a = -gi) : (χ ^ 3) a = -χ a := by
  rw [MulChar.pow_apply' χ (by norm_num), pow_succ]
  have : χ a ^ 2 = -1 := by rcases h with h | h <;> rw [h] <;> simp [gi_sq]
  rw [this]; ring
end BandParity
