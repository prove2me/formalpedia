-- Prove2me | solution 1 for EinsteinFieldEquations.cosmological_constant_as_vacuum_energy
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T19:33:36.568287+00:00
-- url     : https://prove2.me/submissions/c0dc6d1e-3ba0-4116-a645-1119d8f3db6b

import Mathlib
import Definitions.Def_efe_geometry
import Definitions.Def_efe_metrics

open EinsteinFieldEquations

theorem W2c_EinsteinFieldEquations_cc (g T : Tensor2Field) (Lam kappa : ℝ)
    (x : Coord) (hkappa : kappa ≠ 0) :
    SatisfiesEFE g Lam kappa T x ↔
      SatisfiesEFE g 0 kappa (fun y => T y - (Lam / kappa) • g y) x := by
  unfold SatisfiesEFE
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, zero_mul, add_zero]
  have e : ∀ a b : Fin 4, kappa * (T x a b - Lam / kappa * g x a b)
      = kappa * T x a b - Lam * g x a b := by
    intro a b
    field_simp
    try ring
  constructor
  · intro h a b; rw [e]; linarith [h a b]
  · intro h a b; have := h a b; rw [e] at this; linarith

theorem W2c_EinsteinFieldEquations_chr_mink :
    ∀ a b c : Fin 4, christoffel minkowski a b c = fun _ => 0 := by
  intro a b c
  funext x
  unfold christoffel partialD minkowski
  simp

theorem W2c_EinsteinFieldEquations_ricci_mink (b d : Fin 4) (x : Coord) :
    ricci minkowski b d x = 0 := by
  unfold ricci riemann partialD
  simp [W2c_EinsteinFieldEquations_chr_mink]

theorem W2c_EinsteinFieldEquations_minkowski_vacuum (kappa : ℝ) (x : Coord) :
    SatisfiesEFE minkowski 0 kappa (fun _ => 0) x := by
  intro a b
  unfold einsteinTensor scalarCurvature metricTrace
  simp [W2c_EinsteinFieldEquations_ricci_mink]

theorem W2c_EinsteinFieldEquations_schw_inv (M : ℝ) (x : Coord) (hM : 0 < M)
    (hx : SchwarzschildExterior M x) :
    (schwarzschild M x)⁻¹ = Matrix.diagonal ![-(1 - 2 * M / x 1)⁻¹, 1 - 2 * M / x 1,
      ((x 1) ^ 2)⁻¹, ((x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹] := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hr : 0 < x 1 := by linarith
  have hr' : x 1 ≠ 0 := hr.ne'
  have hf : 1 - 2 * M / x 1 ≠ 0 := by
    have : 2 * M / x 1 < 1 := (div_lt_one hr).2 h1
    linarith
  have hs : Real.sin (x 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi h2 h3).ne'
  unfold schwarzschild
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have hf' : x 1 - 2 * M ≠ 0 := by intro h; linarith
  fin_cases i <;> simp [hf, hr', hs] <;> field_simp <;> ring

theorem solution (g T : Tensor2Field) (Lam kappa : ℝ)
    (x : Coord) (hkappa : kappa ≠ 0) :
    SatisfiesEFE g Lam kappa T x ↔
      SatisfiesEFE g 0 kappa (fun y => T y - (Lam / kappa) • g y) x := by
  apply W2c_EinsteinFieldEquations_cc <;> assumption
