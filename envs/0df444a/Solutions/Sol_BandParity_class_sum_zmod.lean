-- Prove2me | solution 1 for BandParity.class_sum_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:19.399028+00:00
-- url     : https://prove2.me/submissions/91d4b6c4-285b-4d49-b976-77b5c11884fa

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_exists_kernel_ne_one
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
theorem _root_.solution (hp5 : 5 < p) (z : GaussianInt) :
    ∑ n : ZMod p, (if χ n = z then n else 0) = 0 := by
  obtain ⟨a, ha0, ha1, hχa⟩ := exists_kernel_ne_one hχ hp5
  set s0 := ∑ n : ZMod p, (if χ n = z then n else 0)
  have h : s0 = a * s0 := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft₀ a ha0) _ _ fun n => ?_).symm
    simp only [Equiv.mulLeft₀_apply, map_mul, hχa, one_mul, mul_ite, mul_zero]
  have : (a - 1) * s0 = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha1)
end BandParity
