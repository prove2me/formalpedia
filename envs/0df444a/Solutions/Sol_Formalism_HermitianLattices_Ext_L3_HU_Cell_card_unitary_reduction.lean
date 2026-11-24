-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Cell.card_unitary_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:50:24.735791+00:00
-- url     : https://prove2.me/submissions/8e7fc22d-8a26-4aa5-b1d4-557275d08c3c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Cell_map_skew
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Cell_quad_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Cell_expand
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_card_eq_mul_of_fibers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open HermitianSublattices idealPowerSpanBounds
open Formalism.HermitianLattices.Ext.L3.HU.Cell
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A A' C : Type*} [CommRing A] [StarRing A] [CommRing A'] [CommRing C] [StarRing C]
namespace Formalism.HermitianLattices.Ext.L3.HU.Cell
theorem _root_.solution [Finite A] (π : A →+* A') (ρ : A →+* C) (μ : C →+ A)
    (hμi : Function.Injective μ) (hμr : ∀ a, π a = 0 ↔ ∃ y, μ y = a)
    (hμs : ∀ y, μ (star y) = star (μ y)) (hμm : ∀ a y, μ (ρ a * y) = a * μ y)
    (h2 : ∀ y z, μ y * μ z = 0) (H : Matrix κ κ A)
    (hu : ∀ X : Matrix κ κ A, Xᴴ * H * X = H → IsUnit X.det) :
    Nat.card {X : Matrix κ κ A // Xᴴ * H * X = H} =
      Nat.card {X' : Matrix κ κ A' // ∃ X : Matrix κ κ A, Xᴴ * H * X = H ∧ X.map π = X'} *
        Nat.card {Y : Matrix κ κ C // H.map ρ * Y + Yᴴ * H.map ρ = 0} := by
  rw [mul_comm]
  apply NormLifting.card_eq_mul_of_fibers (fun X : {X : Matrix κ κ A // Xᴴ * H * X = H} =>
    (⟨X.1.map π, X.1, X.2, rfl⟩ :
      {X' : Matrix κ κ A' // ∃ X : Matrix κ κ A, Xᴴ * H * X = H ∧ X.map π = X'}))
  rintro ⟨X', X0, hX0, rfl⟩
  have hmi : Function.Injective (fun Y : Matrix κ κ C => Y.map μ) := Matrix.map_injective hμi
  have hS : ∀ Y : Matrix κ κ C, H.map ρ * Y + Yᴴ * H.map ρ = 0 →
      (X0 * (1 + Y.map μ))ᴴ * H * (X0 * (1 + Y.map μ)) = H := by
    intro Y hY
    rw [expand hX0, quad_zero μ hμs h2, ← map_skew ρ μ hμs hμm, hY]
    simp
  have hπ : ∀ Y : Matrix κ κ C, (X0 * (1 + Y.map μ)).map π = X0.map π := by
    intro Y
    have h0 : (Y.map μ).map π = 0 := by
      ext i l
      exact (hμr _).2 ⟨_, rfl⟩
    rw [Matrix.map_mul, Matrix.map_add _ (map_add π), h0, add_zero, Matrix.map_one _ (map_zero π) (map_one π),
      Matrix.mul_one]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun Y => ⟨⟨X0 * (1 + Y.1.map μ), hS Y.1 Y.2⟩, Subtype.ext (hπ Y.1)⟩) ⟨?_, ?_⟩)
  · intro Y Y' h
    have h1 : X0 * (1 + Y.1.map μ) = X0 * (1 + Y'.1.map μ) :=
      congrArg (fun z => z.1.1) h
    have h2' := congrArg (fun z => X0⁻¹ * z) h1
    simp only [Matrix.nonsing_inv_mul_cancel_left _ _ (hu X0 hX0)] at h2'
    exact Subtype.ext (hmi (add_left_cancel h2'))
  · rintro ⟨⟨X, hX⟩, hfib⟩
    have hXπ : X.map π = X0.map π := congrArg Subtype.val hfib
    have hD : ∀ i l, ∃ y, μ y = (X0⁻¹ * (X - X0)) i l := by
      intro i l
      rw [← hμr, Matrix.mul_apply, map_sum]
      apply Finset.sum_eq_zero
      intro k _
      have : π (X k l) = π (X0 k l) := congrFun (congrFun hXπ k) l
      rw [map_mul, Matrix.sub_apply, map_sub, this, sub_self, mul_zero]
    choose y hy using hD
    have hYD : (Matrix.of y).map μ = X0⁻¹ * (X - X0) := by
      ext i l
      exact hy i l
    have hXe : X0 * (1 + (Matrix.of y).map μ) = X := by
      rw [hYD, Matrix.mul_add, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ (hu X0 hX0)]
      abel
    have hsk : H.map ρ * Matrix.of y + (Matrix.of y)ᴴ * H.map ρ = 0 := by
      apply hmi
      show (H.map ρ * Matrix.of y + (Matrix.of y)ᴴ * H.map ρ).map μ = (0 : Matrix κ κ C).map μ
      have h3 := expand hX0 ((Matrix.of y).map μ)
      rw [hXe, hX, quad_zero μ hμs h2, add_zero] at h3
      rw [map_skew ρ μ hμs hμm, Matrix.map_zero _ (map_zero μ)]
      exact (left_eq_add.1 h3)
    exact ⟨⟨Matrix.of y, hsk⟩, Subtype.ext (Subtype.ext hXe)⟩
end Formalism.HermitianLattices.Ext.L3.HU.Cell
