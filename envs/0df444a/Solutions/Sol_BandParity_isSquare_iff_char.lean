-- Prove2me | solution 1 for BandParity.isSquare_iff_char
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:06:53.484803+00:00
-- url     : https://prove2.me/submissions/cc2fa4fe-5340-40ed-a9c9-9b1c132f00f4

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_exists_generator
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_gi_sq
public import Theorems.Thm_BandParity_pm_gi_pow_odd
public import Theorems.Thm_BandParity_quartic_apply_generator
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
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : IsSquare x ↔ (χ x = 1 ∨ χ x = -1) := by
  constructor
  · rintro ⟨m, rfl⟩
    have hm : m ≠ 0 := by rintro rfl; simp at hx
    rw [map_mul]
    rcases quartic_values χ hχ hm with h | h | h | h <;> rw [h]
    · left; ring
    · right; rw [← sq, gi_sq]
    · left; ring
    · right; rw [neg_mul_neg, ← sq, gi_sq]
  · intro h
    obtain ⟨g, -, hg⟩ := exists_generator (p := p)
    obtain ⟨j, hj⟩ := hg (Units.mk0 x hx)
    have hxj : x = (g : ZMod p) ^ j := by
      have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hj
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
      exact this.symm
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | hoddj
    · exact ⟨(g : ZMod p) ^ i, by rw [hxj, pow_add]⟩
    · exfalso
      have h' := pm_gi_pow_odd (quartic_apply_generator χ hχ hg) hoddj
      rw [← map_pow, ← hxj] at h'
      rcases h with h | h <;> rcases h' with h' | h' <;> rw [h] at h' <;> revert h' <;> decide
end BandParity
