-- Prove2me | solution 1 for EmpiricalBernstein.SVP.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:03:18.037974+00:00
-- url     : https://prove2.me/submissions/9209da2a-2cb3-4181-9a02-fd6c7a31c6cd

import Mathlib

set_option autoImplicit false

open MeasureTheory

lemma sol_int (ν : Measure ℝ) [IsProbabilityMeasure ν] (a : ℝ)
    (hν : ν (Set.Icc a (a + 1))ᶜ = 0) (f : ℝ → ℝ) (hf : Continuous f) : Integrable f ν := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := a + 1)).exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  have : ∀ᵐ x ∂ν, x ∈ Set.Icc a (a + 1) := by
    rw [ae_iff]; exact hν
  filter_upwards [this] with x hx using hC x hx

lemma sol_poly (ν : Measure ℝ) [IsProbabilityMeasure ν] (a : ℝ)
    (hν : ν (Set.Icc a (a + 1))ᶜ = 0) (c0 c1 c2 c3 c4 : ℝ) :
    ∫ y, (c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4) ∂ν
      = c0 + c1 * ∫ y, y ∂ν + c2 * ∫ y, y ^ 2 ∂ν + c3 * ∫ y, y ^ 3 ∂ν
        + c4 * ∫ y, y ^ 4 ∂ν := by
  have hI := sol_int ν a hν
  have i1 : Integrable (fun y : ℝ => c0 + c1 * y) ν := hI _ (by fun_prop)
  have i2 : Integrable (fun y : ℝ => c2 * y ^ 2) ν := hI _ (by fun_prop)
  have i3 : Integrable (fun y : ℝ => c3 * y ^ 3) ν := hI _ (by fun_prop)
  have i4 : Integrable (fun y : ℝ => c4 * y ^ 4) ν := hI _ (by fun_prop)
  have i5 : Integrable (fun y : ℝ => c0 + c1 * y + c2 * y ^ 2) ν := hI _ (by fun_prop)
  have i6 : Integrable (fun y : ℝ => c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3) ν :=
    hI _ (by fun_prop)
  have i7 : Integrable (fun y : ℝ => c0) ν := hI _ (by fun_prop)
  have i8 : Integrable (fun y : ℝ => c1 * y) ν := hI _ (by fun_prop)
  rw [integral_add i6 i4, integral_add i5 i3, integral_add i1 i2, integral_add i7 i8,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  simp

theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν] (a : ℝ)
    (hν : ν (Set.Icc a (a + 1))ᶜ = 0) :
    ∫ x, (∫ y, (x - y) ^ 2 ∂ν) ^ 2 ∂ν ≤ (1 / 2) * ∫ x, ∫ y, (x - y) ^ 2 ∂ν ∂ν := by
  have hI := sol_int ν a hν
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc a (a + 1) := by
    rw [ae_iff]; exact hν
  set m1 := ∫ y, y ∂ν with hm1
  set m2 := ∫ y, y ^ 2 ∂ν with hm2
  set m3 := ∫ y, y ^ 3 ∂ν with hm3
  set m4 := ∫ y, y ^ 4 ∂ν with hm4
  have hg : ∀ x : ℝ, ∫ y, (x - y) ^ 2 ∂ν = x ^ 2 - 2 * m1 * x + m2 := by
    intro x
    have e : (fun y : ℝ => (x - y) ^ 2)
        = fun y => x ^ 2 + (-2 * x) * y + 1 * y ^ 2 + 0 * y ^ 3 + 0 * y ^ 4 := by
      funext y; ring
    rw [e, sol_poly ν a hν]; ring
  have hh : ∀ x : ℝ, ∫ y, (x - y) ^ 4 ∂ν
      = x ^ 4 - 4 * x ^ 3 * m1 + 6 * x ^ 2 * m2 - 4 * x * m3 + m4 := by
    intro x
    have e : (fun y : ℝ => (x - y) ^ 4)
        = fun y => x ^ 4 + (-4 * x ^ 3) * y + (6 * x ^ 2) * y ^ 2 + (-4 * x) * y ^ 3
            + 1 * y ^ 4 := by
      funext y; ring
    rw [e, sol_poly ν a hν]; ring
  have hL : ∫ x, (∫ y, (x - y) ^ 2 ∂ν) ^ 2 ∂ν = m4 - 4 * m1 * m3 + 3 * m2 ^ 2 := by
    simp_rw [hg]
    have e : (fun x : ℝ => (x ^ 2 - 2 * m1 * x + m2) ^ 2)
        = fun x => m2 ^ 2 + (-4 * m1 * m2) * x + (4 * m1 ^ 2 + 2 * m2) * x ^ 2
            + (-4 * m1) * x ^ 3 + 1 * x ^ 4 := by
      funext x; ring
    rw [e, sol_poly ν a hν]; ring
  have hR : ∫ x, ∫ y, (x - y) ^ 4 ∂ν ∂ν = 2 * (m4 - 4 * m1 * m3 + 3 * m2 ^ 2) := by
    simp_rw [hh]
    have e : (fun x : ℝ => x ^ 4 - 4 * x ^ 3 * m1 + 6 * x ^ 2 * m2 - 4 * x * m3 + m4)
        = fun x => m4 + (-4 * m3) * x + (6 * m2) * x ^ 2 + (-4 * m1) * x ^ 3
            + 1 * x ^ 4 := by
      funext x; ring
    rw [e, sol_poly ν a hν]; ring
  have hmono : ∫ x, ∫ y, (x - y) ^ 4 ∂ν ∂ν ≤ ∫ x, ∫ y, (x - y) ^ 2 ∂ν ∂ν := by
    refine integral_mono_ae ?_ ?_ ?_
    · simp_rw [hh]; exact hI _ (by fun_prop)
    · simp_rw [hg]; exact hI _ (by fun_prop)
    · filter_upwards [hae] with x hx
      refine integral_mono_ae (hI _ (by fun_prop)) (hI _ (by fun_prop)) ?_
      filter_upwards [hae] with y hy
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      have h1 : (x - y) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (x - y), mul_nonneg (sq_nonneg (x - y)) (sub_nonneg.2 h1)]
  rw [hL]
  rw [hR] at hmono
  linarith
