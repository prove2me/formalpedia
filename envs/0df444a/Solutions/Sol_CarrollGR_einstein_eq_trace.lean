-- Prove2me | solution 1 for CarrollGR.einstein_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T19:15:56.074982+00:00
-- url     : https://prove2.me/submissions/691b8789-6822-4414-a8d2-ffe998cc8a89

import Mathlib
import Definitions.Def_CarrollGR_Defs

/-! 62809881 CarrollGR.einstein_eq_trace.
Contract Einstein's equation with g^{μν}: Σ g^{μν} G_{μν} = R - ½ R Σ g^{μν} g_{μν} = R - 2R = -R,
using Σ_{μν} (g⁻¹)_{μν} g_{μν} = 4 (inverse_metric_contraction, re-proved here), while the
right-hand side contracts to 8πG T. -/

set_option autoImplicit false

open scoped ContDiff

namespace CGRBuild

open CarrollGR Matrix

theorem lor_det_ne {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) : M.det ≠ 0 := by
  obtain ⟨P, _, h⟩ := hM
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
  intro h0
  rw [h0] at h2
  simp [minkowskiEta, Matrix.det_diagonal, Fin.prod_univ_four] at h2

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

theorem inv_contract {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, M⁻¹ μ ν * M μ ν = 4 := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr (lor_det_ne hM)
  have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hu
  have e : ∀ μ, ∑ ν : Fin 4, M⁻¹ μ ν * M μ ν = (M⁻¹ * M) μ μ := by
    intro μ
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [lor_symm' hM μ ν]
  simp_rw [e, h1]
  simp [Fin.sum_univ_four, Matrix.one_apply]

theorem einstein_trace' (g T : TensorField2) (GN : ℝ) (x : Coord) (hg : IsLorentzian (g x))
    (hE : EinsteinEq g GN T x) :
    -ricciScalar g x = 8 * Real.pi * GN * metricTrace g T x := by
  have hc := inv_contract hg
  have hp : ∀ μ ν, invMetric g x μ ν * einstein g μ ν x
      = invMetric g x μ ν * ricci g μ ν x
        - (1 / 2 : ℝ) * ricciScalar g x * ((g x)⁻¹ μ ν * g x μ ν) := by
    intro μ ν
    unfold einstein invMetric
    ring
  have h1 : ∑ μ : Fin 4, ∑ ν : Fin 4, invMetric g x μ ν * einstein g μ ν x
      = ricciScalar g x - (1 / 2 : ℝ) * ricciScalar g x * 4 := by
    simp only [hp, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hc]
    rfl
  have h2 : ∑ μ : Fin 4, ∑ ν : Fin 4, invMetric g x μ ν * einstein g μ ν x
      = 8 * Real.pi * GN * metricTrace g T x := by
    simp only [metricTrace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [hE μ ν]
    ring
  linarith

end CGRBuild

open CarrollGR in open scoped ContDiff in
theorem solution (g T : TensorField2) (GN : ℝ) (x : Coord) (hg : IsLorentzian (g x))
    (hE : EinsteinEq g GN T x) :
    -ricciScalar g x = 8 * Real.pi * GN * metricTrace g T x := by
  exact CGRBuild.einstein_trace' g T GN x hg hE
