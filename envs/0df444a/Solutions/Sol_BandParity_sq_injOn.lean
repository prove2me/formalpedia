-- Prove2me | solution 1 for BandParity.sq_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:54.030939+00:00
-- url     : https://prove2.me/submissions/3abdb12b-bed7-43a7-9a58-01a4aacf6e03

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_mem_cls
public import Theorems.Thm_BandParity_char_neg
public import Theorems.Thm_BandParity_quartic_apply_neg_one


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) {z : GaussianInt} (hz : z ≠ 0) :
    Set.InjOn (fun x : ZMod p => x ^ 2) (cls χ z : Set (ZMod p)) := by
  have hodd := quartic_apply_neg_one χ hχ hp8
  intro u hu v hv h
  rw [mem_cls] at hu hv
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact h
  · exfalso
    rw [h, char_neg hodd, hv] at hu
    exact hz (self_eq_neg.1 hu.symm)
end BandParity
