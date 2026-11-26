-- Prove2me | solution 1 for BandParity.exists_kernel_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:29.615347+00:00
-- url     : https://prove2.me/submissions/8f02dae7-7154-4c3e-89c5-9c5308c6e5e7

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_exists_generator
public import Theorems.Thm_BandParity_unit_apply_pow_four


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp5 : 5 < p) : ∃ a : ZMod p, a ≠ 0 ∧ a ≠ 1 ∧ χ a = 1 := by
  obtain ⟨g, hgo, -⟩ := exists_generator (p := p)
  refine ⟨((g ^ 4 : (ZMod p)ˣ) : ZMod p), Units.ne_zero _, fun h => ?_, ?_⟩
  · have h1 : g ^ 4 = 1 := Units.ext h
    have := Nat.le_of_dvd (by norm_num) (hgo ▸ orderOf_dvd_of_pow_eq_one h1)
    omega
  · rw [Units.val_pow_eq_pow_val, map_pow]
    exact unit_apply_pow_four χ hχ g
end BandParity
