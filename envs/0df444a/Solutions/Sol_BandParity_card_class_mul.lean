-- Prove2me | solution 1 for BandParity.card_class_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:38.686192+00:00
-- url     : https://prove2.me/submissions/09e8eb81-f24c-4ca7-9e27-b8bce588132b

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_apply_eq_zero_iff
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
theorem _root_.solution {c : ZMod p} (hc : c ≠ 0) (z : GaussianInt) :
    (univ.filter (fun n : ZMod p => χ n = χ c * z)).card =
      (univ.filter (fun n : ZMod p => χ n = z)).card := by
  symm
  refine Finset.card_equiv (Equiv.mulLeft₀ c hc) fun n => ?_
  simp only [mem_filter, mem_univ, true_and, Equiv.mulLeft₀_apply, map_mul]
  have hχc : χ c ≠ 0 := fun h => hc ((apply_eq_zero_iff hχ).1 h)
  exact ⟨fun h => h ▸ rfl, fun h => mul_left_cancel₀ hχc h⟩
end BandParity
