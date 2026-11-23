-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts.card_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:12.245669+00:00
-- url     : https://prove2.me/submissions/836c2874-7cc9-48b0-82b5-50a536c10bdd

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardMapEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
open Matrix
variable {A k : Type*} [CommRing A] [StarRing A] [Field k]
variable {m : Type*} [Fintype m] [DecidableEq m]
private theorem map_conjTranspose_mul_mul_eq (φ : A →+* k) (X H : Matrix m m A) :
    (Xᴴ * H * X).map φ = (X.map fun a => φ (star a))ᵀ * H.map φ * X.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
private theorem map_star_eq_transpose_map_of_isHermitian (φ : A →+* k) {M : Matrix m m A} (hM : Mᴴ = M) :
    M.map (fun a => φ (star a)) = (M.map φ)ᵀ := by
  ext i j
  have h := congrFun (congrFun hM j) i
  rw [conjTranspose_apply] at h
  simp only [map_apply, transpose_apply]
  rw [h]
private theorem matrix_eq_of_map_and_map_star_eq (φ : A →+* k) (hb : Function.Bijective fun a : A => (φ (star a), φ a))
    {M N : Matrix m m A} (h1 : M.map φ = N.map φ)
    (h2 : M.map (fun a => φ (star a)) = N.map (fun a => φ (star a))) : M = N := by
  ext i j
  apply hb.1
  exact Prod.ext (congrFun (congrFun h2 i) j) (congrFun (congrFun h1 i) j)
end Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
open Matrix
variable {A k : Type*} [CommRing A] [StarRing A] [Field k]
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
theorem _root_.solution (φ : A →+* k) (hb : Function.Bijective fun a : A => (φ (star a), φ a))
    (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} = Nat.card (GL m k) := by
  classical
  have hdet : (H.map φ).det = φ H.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hGu : IsUnit (H.map φ).det := by
    rw [hdet]; exact hu.map φ
  have cond : ∀ X : Matrix m m A, Xᴴ * H * X = H ↔
      (X.map fun a => φ (star a))ᵀ * H.map φ * X.map φ = H.map φ := by
    intro X
    rw [← map_conjTranspose_mul_mul_eq]
    constructor
    · intro h; rw [h]
    · intro h
      apply matrix_eq_of_map_and_map_star_eq φ hb h
      have hM : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
        simp [conjTranspose_mul, hH, Matrix.mul_assoc]
      rw [map_star_eq_transpose_map_of_isHermitian φ hM, map_star_eq_transpose_map_of_isHermitian φ hH, h]
  have hP : ∀ X : {X : Matrix m m A // Xᴴ * H * X = H}, IsUnit (X.1.map φ).det := by
    intro X
    have h := congrArg Matrix.det ((cond X.1).mp X.2)
    rw [det_mul, det_mul] at h
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero] at h
    exact hGu.ne_zero h.symm
  have key : ∀ X : {X : Matrix m m A // Xᴴ * H * X = H},
      (X.1.map fun a => φ (star a))ᵀ = H.map φ * (H.map φ * X.1.map φ)⁻¹ := by
    intro X
    have h := (cond X.1).mp X.2
    have hu' : IsUnit (H.map φ * X.1.map φ).det := by
      rw [det_mul]; exact hGu.mul (hP X)
    calc (X.1.map fun a => φ (star a))ᵀ
        = (X.1.map fun a => φ (star a))ᵀ * (H.map φ * X.1.map φ) * (H.map φ * X.1.map φ)⁻¹ := by
          rw [Matrix.mul_assoc _ (H.map φ * X.1.map φ), Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
      _ = H.map φ * (H.map φ * X.1.map φ)⁻¹ := by
          rw [← Matrix.mul_assoc _ (H.map φ), h]
  refine Nat.card_eq_of_bijective (fun X => Matrix.nonsingInvUnit (X.1.map φ) (hP X)) ⟨?_, ?_⟩
  · intro X Y hXY
    have hPe : X.1.map φ = Y.1.map φ := congrArg Units.val hXY
    have hQe : X.1.map (fun a => φ (star a)) = Y.1.map (fun a => φ (star a)) := by
      calc X.1.map (fun a => φ (star a)) = ((X.1.map fun a => φ (star a))ᵀ)ᵀ :=
            (transpose_transpose _).symm
        _ = (H.map φ * (H.map φ * Y.1.map φ)⁻¹)ᵀ := by rw [key X, hPe]
        _ = Y.1.map (fun a => φ (star a)) := by rw [← key Y, transpose_transpose]
    exact Subtype.ext (matrix_eq_of_map_and_map_star_eq φ hb hPe hQe)
  · intro U
    let e := Equiv.ofBijective _ hb
    let X : Matrix m m A := Matrix.of fun i j =>
      e.symm ((H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ i j, (↑U : Matrix m m k) i j)
    have hX : ∀ i j, (φ (star (X i j)), φ (X i j)) =
        ((H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ i j, (↑U : Matrix m m k) i j) :=
      fun i j => e.apply_symm_apply _
    have hXP : X.map φ = (↑U : Matrix m m k) := by
      ext i j; exact congrArg Prod.snd (hX i j)
    have hXQ : X.map (fun a => φ (star a)) = (H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ := by
      ext i j; exact congrArg Prod.fst (hX i j)
    have hc : Xᴴ * H * X = H := by
      rw [cond, hXP, hXQ, transpose_transpose]
      calc H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹ * H.map φ * (↑U : Matrix m m k)
          = H.map φ * (↑U⁻¹ : Matrix m m k) * ((H.map φ)⁻¹ * H.map φ) * (↑U : Matrix m m k) := by
            simp only [Matrix.mul_assoc]
        _ = H.map φ := by
            rw [Matrix.nonsing_inv_mul _ hGu, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul,
              Matrix.mul_one]
    refine ⟨⟨X, hc⟩, ?_⟩
    apply Units.ext
    exact hXP
end Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
