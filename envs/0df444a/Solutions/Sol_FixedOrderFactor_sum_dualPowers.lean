-- Prove2me | solution 1 for FixedOrderFactor.sum_dualPowers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:06.733117+00:00
-- url     : https://prove2.me/submissions/3cca9aff-65e0-44ba-8306-2a94939a98b7

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
public import Theorems.Thm_FixedOrderFactor_symm_dualPowers

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]
namespace FixedOrderFactor
theorem _root_.solution (r : ℕ) (u : (ZMod p)ˣ) :
    ∑ χ : dualPowers p r, (χ : MulChar (ZMod p) ℂ) u =
      if u ∈ powers p r then (Nat.card (dualPowers p r) : ℂ) else 0 := by
  classical
  split_ifs with hu
  · have : ∀ χ : dualPowers p r, (χ : MulChar (ZMod p) ℂ) u = 1 := fun χ =>
      ((MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff).mp χ.2) u hu
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  · have hne : ¬ ∀ χ ∈ dualPowers p r, χ u = 1 := by
      intro h; apply hu
      rw [← symm_dualPowers]
      exact MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff.mpr h
    push Not at hne
    obtain ⟨χ₀, hχ₀, h1⟩ := hne
    set S := ∑ χ : dualPowers p r, (χ : MulChar (ZMod p) ℂ) u
    have hS : (χ₀ : MulChar (ZMod p) ℂ) u * S = S := by
      rw [Finset.mul_sum]
      exact Fintype.sum_equiv (Equiv.mulLeft (⟨χ₀, hχ₀⟩ : dualPowers p r)) _ _
        (fun χ => by simp [MulChar.coeToFun_mul])
    have : (χ₀ u - 1) * S = 0 := by linear_combination hS
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h1
    · exact h
end FixedOrderFactor
