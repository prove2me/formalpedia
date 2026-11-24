-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts.card_inert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:34.441423+00:00
-- url     : https://prove2.me/submissions/feaba3f3-e0ef-4e8e-8f1f-e9ae14430a0c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardMapEquiv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_UnitaryNormCounts_card_conj
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_UnitaryNormCounts_card_map_equiv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_UnitaryNormCounts_exists_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
open Matrix
variable {A k : Type*} [CommRing A] [StarRing A] [Field k]
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
theorem _root_.solution [Fintype k] (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a))
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (u : m → A) (hu : ∀ i, star (u i) = u i) (hunit : ∀ i, IsUnit (u i)) :
    Nat.card {X : Matrix m m A // Xᴴ * diagonal u * X = diagonal u} =
      Nat.card {X : Matrix m m k // (X.map σ).transpose * X = 1} := by
  have hy : ∀ i, ∃ y, σ y * y = φ (u i) := fun i =>
    exists_norm σ hσ hne q hq (φ (u i)) (by rw [← hφ, hu])
  choose y hy using hy
  set a : m → A := fun i => φ.symm (y i) with ha_def
  have ha : ∀ i, star (a i) * a i = u i := by
    intro i
    apply φ.injective
    rw [map_mul, hφ]
    simp [ha_def, hy]
  have hCC : (diagonal a)ᴴ * diagonal a = diagonal u := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    exact ha i
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [ha i]; exact hunit i)
  have hC : IsUnit (diagonal a).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr hau))
  rw [← hCC, card_conj (diagonal a) hC, card_map_equiv φ σ hφ]
end Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
