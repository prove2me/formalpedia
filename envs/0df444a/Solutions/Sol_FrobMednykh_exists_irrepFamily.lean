-- Prove2me | solution 1 for FrobMednykh.exists_irrepFamily
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:51:02.008563+00:00
-- url     : https://prove2.me/submissions/50548392-8cbb-4c04-9b1b-ea80016ba800

import Mathlib
import Definitions.Def_FrobMednykh_defs

open CategoryTheory
open FrobMednykh
theorem fm_card_ne_zero (G : Type) [Group G] [Fintype G] : (Nat.card G : ℂ) ≠ 0 := by
  rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero

open Classical in
theorem fm_pair {G : Type} [Group G] [Fintype G] (V W : FDRep ℂ G) [Simple V] [Simple W] :
    ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then (Nat.card G : ℂ) else 0 := by
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (fm_card_ne_zero G)
  have h := FDRep.char_orthonormal V W
  have h2 : ∑ g : G, V.character g * W.character g⁻¹ =
      (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹) := by
    rw [← mul_assoc, mul_inv_cancel₀ (fm_card_ne_zero G), one_mul]
  rw [h2, h]
  split_ifs <;> simp

theorem fm_iso_of_char_eq {G : Type} [Group G] [Fintype G] (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : V.character = W.character) : Nonempty (V ≅ W) := by
  classical
  have h1 := fm_pair V W
  have h2 := fm_pair V V
  rw [if_pos ⟨Iso.refl V⟩] at h2
  rw [← h, h2] at h1
  by_contra hn
  rw [if_neg hn] at h1
  exact fm_card_ne_zero G h1

theorem fm_exists_irrepFamily (G : Type) [Group G] [Fintype G] :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (IrrepFamily G ι) := by
  classical
  let S : Set (G → ℂ) := {χ | ∃ W : FDRep ℂ G, Simple W ∧ W.character = χ}
  have hli : LinearIndependent ℂ (fun χ : S => (χ : G → ℂ)) := by
    rw [linearIndependent_iff']
    intro s c hs i hi
    obtain ⟨Wi, hWi, hci⟩ := i.2
    have key : ∀ j : S, ∑ g : G, (j : G → ℂ) g * Wi.character g⁻¹ =
        if j = i then (Nat.card G : ℂ) else 0 := by
      intro j
      obtain ⟨Wj, hWj, hcj⟩ := j.2
      rw [← hcj, fm_pair Wj Wi]
      by_cases hji : j = i
      · rw [if_pos hji, if_pos]
        exact fm_iso_of_char_eq Wj Wi (hcj.trans ((congrArg Subtype.val hji).trans hci.symm))
      · rw [if_neg hji, if_neg]
        rintro ⟨e⟩
        apply hji
        apply Subtype.ext
        rw [← hcj, ← hci, FDRep.char_iso e]
    have := congrArg (fun f : G → ℂ => ∑ g : G, f g * Wi.character g⁻¹) hs
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero] at this
    simp only [Finset.sum_mul] at this
    rw [Finset.sum_comm] at this
    simp only [mul_assoc, ← Finset.mul_sum, key, mul_ite, mul_zero] at this
    rw [Finset.sum_ite_eq' s i, if_pos hi] at this
    exact (mul_eq_zero.mp this).resolve_right (fm_card_ne_zero G)
  have hfin : Finite S := hli.finite_of_isNoetherian
  refine ⟨S, Fintype.ofFinite S, ⟨?_⟩⟩
  exact {
    V := fun χ => χ.2.choose
    simple := fun χ => χ.2.choose_spec.1
    injective := fun i j ⟨e⟩ => by
      apply Subtype.ext
      rw [← i.2.choose_spec.2, ← j.2.choose_spec.2, FDRep.char_iso e]
    complete := fun W hW => by
      refine ⟨⟨W.character, W, hW, rfl⟩, ?_⟩
      have hs := (⟨W.character, W, hW, rfl⟩ : S).2.choose_spec
      have := hs.1
      exact fm_iso_of_char_eq _ _ hs.2.symm }

theorem solution (G : Type) [Group G] [Fintype G] :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (IrrepFamily G ι) := by
  exact fm_exists_irrepFamily G


