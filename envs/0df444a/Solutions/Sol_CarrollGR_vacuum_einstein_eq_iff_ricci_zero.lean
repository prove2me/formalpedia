-- Prove2me | solution 1 for CarrollGR.vacuum_einstein_eq_iff_ricci_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T14:08:35.047625+00:00
-- url     : https://prove2.me/submissions/54d6efb3-885d-4239-8837-ae8ed655050d

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

open Matrix in
theorem vacuum_einstein_eq_iff_ricci_zero_aux (g : TensorField2) (x : Coord)
    (hg : IsLorentzian (g x)) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, (g x)⁻¹ μ ν * g x μ ν = 4 := by
  obtain ⟨P, hP, hPg⟩ := hg
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hP
  have hPTu : IsUnit Pᵀ := (Matrix.isUnit_iff_isUnit_det Pᵀ).mpr (by rw [Matrix.det_transpose]; exact hP)
  have hsym : (g x)ᵀ = g x := by
    have h1 : Pᵀ * (g x)ᵀ * P = Pᵀ * g x * P := by
      have e : (Pᵀ * g x * P)ᵀ = Pᵀ * (g x)ᵀ * P := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [← e, hPg]
      simp [minkowskiEta]
    have h2 := hPu.mul_right_cancel h1
    exact hPTu.mul_left_cancel h2
  have hdet : IsUnit (g x).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det hPg
    rw [Matrix.det_mul, Matrix.det_mul, h0] at this
    simp [minkowskiEta, Matrix.det_diagonal, Fin.prod_univ_four] at this
  have hrow : ∀ μ : Fin 4, ∑ ν : Fin 4, (g x)⁻¹ μ ν * g x μ ν = ((g x)⁻¹ * (g x)ᵀ) μ μ := by
    intro μ
    simp [Matrix.mul_apply]
  simp_rw [hrow, hsym, Matrix.nonsing_inv_mul _ hdet]
  simp

end CarrollGR

open CarrollGR in
theorem solution (g : TensorField2) (GN : ℝ) (x : Coord)
    (hg : IsLorentzian (g x)) :
    EinsteinEq g GN (fun _ => 0) x ↔ ∀ μ ν : Fin 4, ricci g μ ν x = 0 := by
  have htr := CarrollGR.vacuum_einstein_eq_iff_ricci_zero_aux g x hg
  constructor
  · intro h
    have hr : ∀ μ ν : Fin 4, ricci g μ ν x = (1 / 2) * ricciScalar g x * g x μ ν := by
      intro μ ν
      have := h μ ν
      unfold einstein at this
      simp only [Matrix.zero_apply, mul_zero] at this
      linarith
    have hR : ricciScalar g x = 0 := by
      have e : ricciScalar g x
          = ∑ μ : Fin 4, ∑ ν : Fin 4, (g x)⁻¹ μ ν * ((1 / 2) * ricciScalar g x * g x μ ν) := by
        conv_lhs => rw [show ricciScalar g x
          = ∑ μ : Fin 4, ∑ ν : Fin 4, (g x)⁻¹ μ ν * ricci g μ ν x from rfl]
        simp_rw [hr]
      have e2 : ∑ μ : Fin 4, ∑ ν : Fin 4, (g x)⁻¹ μ ν * ((1 / 2) * ricciScalar g x * g x μ ν)
          = (1 / 2) * ricciScalar g x * ∑ μ : Fin 4, ∑ ν : Fin 4, (g x)⁻¹ μ ν * g x μ ν := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ν _ => ?_)
        ring
      rw [e2, htr] at e
      linarith
    intro μ ν
    rw [hr, hR]
    simp
  · intro h μ ν
    have hR : ricciScalar g x = 0 := by
      unfold ricciScalar
      simp [h]
    unfold einstein
    rw [h, hR]
    simp
