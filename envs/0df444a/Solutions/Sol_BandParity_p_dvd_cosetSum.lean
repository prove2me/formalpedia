-- Prove2me | solution 1 for BandParity.p_dvd_cosetSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:57:05.664718+00:00
-- url     : https://prove2.me/submissions/1ae06672-881b-4657-a6f9-925bcbe29fa6

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_cosetSum_eq_sum_ite
public import Theorems.Thm_BandParity_class_sum_zmod
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
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
theorem _root_.solution (hp5 : 5 < p) (z : GaussianInt) : (p : ℤ) ∣ cosetSum χ z := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, cosetSum_eq_sum_ite, Int.cast_sum]
  rw [← class_sum_zmod hχ hp5 z]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp
end BandParity
