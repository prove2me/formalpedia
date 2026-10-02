-- Prove2me | solution 1 for CarrollGR.einstein_eq_iff_trace_reversed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T14:08:31.382691+00:00
-- url     : https://prove2.me/submissions/6311db89-71e1-4c3c-8ec4-3787a9f5f500

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

lemma p43a_lin (W A B : Matrix (Fin 4) (Fin 4) ℝ) (a b : ℝ) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, W μ ν * (a * A μ ν + b * B μ ν)
      = a * ∑ μ : Fin 4, ∑ ν : Fin 4, W μ ν * A μ ν
        + b * ∑ μ : Fin 4, ∑ ν : Fin 4, W μ ν * B μ ν := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma p43a_trace (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : IsLorentzian M) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, M⁻¹ μ ν * M μ ν = 4 := by
  obtain ⟨P, hP, hPM⟩ := hM
  have hPdet : P.det ≠ 0 := hP.ne_zero
  have hdet : M.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hPM
    rw [Matrix.det_mul, Matrix.det_mul, h0] at this
    simp [minkowskiEta, Matrix.det_diagonal, Fin.prod_univ_four] at this
  have hsym : M.transpose = M := by
    have hη : minkowskiEta.transpose = minkowskiEta := by
      simp [minkowskiEta, Matrix.diagonal_transpose]
    have h2 : P.transpose * M.transpose * P = P.transpose * M * P := by
      have := congrArg Matrix.transpose hPM
      rw [hη, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
      rw [hPM, ← this, Matrix.mul_assoc]
    have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hP
    have hPTu : IsUnit P.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr (by rwa [Matrix.det_transpose])
    have h3 : P.transpose * M.transpose = P.transpose * M := hPu.mul_left_injective h2
    exact hPTu.mul_right_injective h3
  have htr : (M⁻¹ * M).trace = 4 := by
    rw [Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)]
    simp
  rw [← htr, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  have : M μ ν = M ν μ := by
    have := congrFun (congrFun hsym ν) μ
    simpa [Matrix.transpose_apply] using this
  rw [this]

end CarrollGR

open CarrollGR in
theorem solution (g T : TensorField2) (GN : ℝ) (x : Coord)
    (hg : IsLorentzian (g x)) :
    EinsteinEq g GN T x ↔
      ∀ μ ν : Fin 4, ricci g μ ν x
        = 8 * Real.pi * GN * (T x μ ν - (1 / 2 : ℝ) * metricTrace g T x * g x μ ν) := by
  have h4 := p43a_trace (g x) hg
  set M := g x with hMdef
  set k := 8 * Real.pi * GN with hk
  set R : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun μ ν => ricci g μ ν x with hR
  set τ := metricTrace g T x with hτ
  have hτ' : τ = ∑ μ : Fin 4, ∑ ν : Fin 4, M⁻¹ μ ν * T x μ ν := rfl
  have hS : ricciScalar g x = ∑ μ : Fin 4, ∑ ν : Fin 4, M⁻¹ μ ν * R μ ν := rfl
  unfold EinsteinEq einstein
  constructor
  · intro h
    have hRe : ∀ μ ν, R μ ν = k * T x μ ν + (1 / 2 * ricciScalar g x) * M μ ν := by
      intro μ ν
      have := h μ ν
      simp only [hR, Matrix.of_apply]
      linarith
    have hSv : ricciScalar g x = -(k * τ) := by
      have e := hS
      simp only [hRe] at e
      rw [p43a_lin, h4, ← hτ'] at e
      linarith
    intro μ ν
    have := hRe μ ν
    simp only [hR, Matrix.of_apply] at this
    rw [this, hSv]
    ring
  · intro h
    have hRe : ∀ μ ν, R μ ν = k * T x μ ν + (-(1 / 2) * k * τ) * M μ ν := by
      intro μ ν
      simp only [hR, Matrix.of_apply]
      rw [h μ ν]
      ring
    have hSv : ricciScalar g x = -(k * τ) := by
      have e := hS
      simp only [hRe] at e
      rw [p43a_lin, h4, ← hτ'] at e
      linarith
    intro μ ν
    have := hRe μ ν
    simp only [hR, Matrix.of_apply] at this
    rw [this, hSv]
    ring
