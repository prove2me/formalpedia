-- Prove2me | solution 1 for BandParity.pow_three_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:54.240651+00:00
-- url     : https://prove2.me/submissions/e2e65b7b-5194-4c00-94ec-a69d8620c6c0

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
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
theorem _root_.solution (n : ZMod p) : (χ ^ 3) n = star (χ n) := by
  by_cases hn : n = 0
  · subst hn; simp [MulChar.map_zero]
  · rw [MulChar.pow_apply' χ (by norm_num)]
    rcases quartic_values χ hχ hn with h | h | h | h <;> rw [h] <;> decide
end BandParity
