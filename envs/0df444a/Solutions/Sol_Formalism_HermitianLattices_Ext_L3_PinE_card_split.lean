-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinE.card_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:15.583918+00:00
-- url     : https://prove2.me/submissions/977881cf-6c86-4cee-be58-636c9d90c3ab

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinE_form_block
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_PinE_block_mulVec_e__244e61ee0901
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinE_eq_block_of_fix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinE_form_col
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinE
variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.HermitianLattices.Ext.L3.PinE
theorem _root_.solution [Finite A] (H' : Matrix κ κ A)
    (htr : ∀ x : Unit ⊕ κ → A, star x ⬝ᵥ (HH H' *ᵥ x) = 1 →
      ∃ G G' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A, Gᴴ * HH H' * G = HH H' ∧ G * G' = 1 ∧ G *ᵥ e₀ = x) :
    Nat.card {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} =
      Nat.card {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} *
        Nat.card {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} := by
  classical
  choose G G' hG using htr
  have h00 : HH H' (Sum.inl ()) (Sum.inl ()) = (1 : A) := by simp [HH]
  have hinv : ∀ x hx, G' x hx * G x hx = 1 := fun x hx => by
    first
      | exact mul_eq_one_comm.mp (hG x hx).2.1
      | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) (hG x hx).2.1
      | exact (Matrix.mul_eq_one_comm (M := G x hx) (N := G' x hx)).mp (hG x hx).2.1
  have hG'form : ∀ x hx, (G' x hx)ᴴ * HH H' * G' x hx = HH H' := by
    intro x hx
    calc (G' x hx)ᴴ * HH H' * G' x hx = (G' x hx)ᴴ * ((G x hx)ᴴ * HH H' * G x hx) * G' x hx := by
          rw [(hG x hx).1]
      _ = (G x hx * G' x hx)ᴴ * HH H' * (G x hx * G' x hx) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = HH H' := by rw [(hG x hx).2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hGeq : ∀ x y (hx : star x ⬝ᵥ (HH H' *ᵥ x) = 1) (hy : star y ⬝ᵥ (HH H' *ᵥ y) = 1), x = y →
      G x hx = G y hy ∧ G' x hx = G' y hy := by
    rintro x _ hx hy rfl
    exact ⟨rfl, rfl⟩
  have fixY : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'),
      (G' (X *ᵥ e₀) (form_col hX h00) * X)ᴴ * HH H' * (G' (X *ᵥ e₀) (form_col hX h00) * X) = HH H' ∧
      (G' (X *ᵥ e₀) (form_col hX h00) * X) *ᵥ e₀ = e₀ := by
    intro X hX
    constructor
    · calc _ = Xᴴ * ((G' (X *ᵥ e₀) (form_col hX h00))ᴴ * HH H' * G' (X *ᵥ e₀) (form_col hX h00)) * X := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = HH H' := by rw [hG'form, hX]
    · have h1 : G' (X *ᵥ e₀) (form_col hX h00) *ᵥ (G (X *ᵥ e₀) (form_col hX h00) *ᵥ e₀) = e₀ := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [(hG _ _).2.2] at h1
      rw [← Matrix.mulVec_mulVec]
      exact h1
  have recon : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'),
      X = G (X *ᵥ e₀) (form_col hX h00) *
        fromBlocks 1 0 0 (G' (X *ᵥ e₀) (form_col hX h00) * X).toBlocks₂₂ := by
    intro X hX
    rw [← (eq_block_of_fix (fixY X hX).1 (fixY X hX).2).2, ← Matrix.mul_assoc, (hG _ _).2.1,
      Matrix.one_mul]
  let f : {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} →
      {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} × {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} :=
    fun X => (⟨X.1 *ᵥ e₀, form_col X.2 h00⟩,
      ⟨_, (eq_block_of_fix (fixY X.1 X.2).1 (fixY X.1 X.2).2).1⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨X1, hX1⟩ ⟨X2, hX2⟩ h
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨hGG, hGG'⟩ := hGeq _ _ (form_col hX1 h00) (form_col hX2 h00) h1
      apply Subtype.ext
      dsimp only
      rw [recon X1 hX1, recon X2 hX2, hGG, h2]
    · rintro ⟨⟨x, hx⟩, ⟨X', hX'⟩⟩
      have hform : (G x hx * fromBlocks 1 0 0 X')ᴴ * HH H' * (G x hx * fromBlocks 1 0 0 X') = HH H' := by
        calc _ = (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A)ᴴ * ((G x hx)ᴴ * HH H' * G x hx) *
              fromBlocks 1 0 0 X' := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = HH H' := by rw [(hG x hx).1, form_block, hX']; rfl
      have hxe : (G x hx * fromBlocks 1 0 0 X') *ᵥ e₀ = x := by
        rw [← Matrix.mulVec_mulVec, block_mulVec_e₀, (hG x hx).2.2]
      refine ⟨⟨_, hform⟩, ?_⟩
      simp only [f]
      obtain ⟨_, hGG'⟩ := hGeq _ _ (form_col hform h00) hx hxe
      refine Prod.ext (Subtype.ext hxe) (Subtype.ext ?_)
      dsimp only
      rw [hGG', ← Matrix.mul_assoc, hinv, Matrix.one_mul, Matrix.toBlocks_fromBlocks₂₂]
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective f hf)
end Formalism.HermitianLattices.Ext.L3.PinE
