-- Prove2me | solution 1 for CarrollGR.christoffel_symm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T18:50:10.793986+00:00
-- url     : https://prove2.me/submissions/d4828c5a-6c05-47ee-a65d-c3e6b2f82b93

import Mathlib
import Definitions.Def_CarrollGR_Defs

/-! 82d55b7e CarrollGR.christoffel_symm.
On the open set U every g y is Lorentzian, hence symmetric, so y ↦ g y a b and y ↦ g y b a
agree near x and have the same partial derivatives (EventuallyEq.fderiv_eq). Unfolding the
Christoffel symbols, the summands for (μ,ν) and (ν,μ) then agree by ring. -/

set_option autoImplicit false

open scoped ContDiff

namespace CGRBuild

open CarrollGR Matrix

theorem lor_symm {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) : Mᵀ = M := by
  obtain ⟨P, hP, h⟩ := hM
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hP
  have hPtu : IsUnit Pᵀ := (Matrix.isUnit_iff_isUnit_det Pᵀ).mpr (by rw [Matrix.det_transpose]; exact hP)
  have ht : Pᵀ * Mᵀ * P = minkowskiEta := by
    have h' := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h'
    rw [Matrix.mul_assoc, h']
    simp [minkowskiEta, Matrix.diagonal_transpose]
  have e : Pᵀ * Mᵀ * P = Pᵀ * M * P := by rw [ht, h]
  exact hPtu.mul_left_cancel (hPu.mul_right_cancel e)

theorem lor_symm' {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) (a b : Fin 4) :
    M a b = M b a := by
  have h := congrFun (congrFun (lor_symm hM) b) a
  rw [Matrix.transpose_apply] at h
  exact h

theorem pd_symm {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (ρ a b : Fin 4) :
    partialD ρ (fun y => g y a b) x = partialD ρ (fun y => g y b a) x := by
  have hev : (fun y => g y a b) =ᶠ[nhds x] (fun y => g y b a) := by
    filter_upwards [hg.1.mem_nhds hx] with y hy
    exact lor_symm' (hg.2.2 y hy) a b
  unfold partialD
  rw [hev.fderiv_eq]

theorem christoffel_symm' (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (σ μ ν : Fin 4) :
    christoffel g σ μ ν x = christoffel g σ ν μ x := by
  unfold christoffel
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [pd_symm hg hx μ ν ρ, pd_symm hg hx ν ρ μ, pd_symm hg hx ρ μ ν]
  ring

end CGRBuild

open CarrollGR in open scoped ContDiff in
theorem solution (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (σ μ ν : Fin 4) :
    christoffel g σ μ ν x = christoffel g σ ν μ x := by
  exact CGRBuild.christoffel_symm' g U hg x hx σ μ ν
