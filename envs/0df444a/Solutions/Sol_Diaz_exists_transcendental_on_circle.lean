-- Prove2me | solution 1 for Diaz.exists_transcendental_on_circle
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:27:25.598737+00:00
-- url     : https://prove2.me/submissions/e9b7b4d6-0471-48fb-81a7-392cf4df5e7c

import Mathlib
import Theorems.Thm_Diaz_transcendental_of_candidate

namespace Diaz

section
open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

/-- `e^i` is transcendental over `ℚ`.  Immediate from Hermite–Lindemann,
since `i` is algebraic and non-zero. -/
theorem transcendental_exp_I : Transcendental ℚ (Complex.exp Complex.I) := by
  intro hcon
  refine (transcendental_of_candidate Complex.I_ne_zero hcon)
    ⟨Polynomial.X ^ 2 - Polynomial.C (-1 : ℚ),
      (Polynomial.monic_X_pow_sub_C (-1 : ℚ) (by norm_num)).ne_zero, ?_⟩
  simp [Complex.I_sq]
end

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

/-- Transcendence over `ℚ` upgrades to transcendence over any base
algebraic over `ℚ` — in particular over the algebraic numbers, which is
the intended base.

Without this the imported axiom is a dead leaf: the results above take
transcendence over the base as a hypothesis, while Hermite–Lindemann
supplies it only over `ℚ`. The algebraicity hypothesis is necessary
rather than decorative: for a base containing `u` the conclusion is
false. -/
theorem transcendental_of_base {L : Subfield ℂ} [Algebra.IsAlgebraic ℚ (↥L)]
    {z : ℂ} (h : Transcendental ℚ z) : Transcendental (↥L) z :=
  fun hcon => h (hcon.restrictScalars ℚ)
end

end Diaz

section
open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

open Diaz in
theorem solution {L : Subfield ℂ}
    [Algebra.IsAlgebraic ℚ (↥L)] {r : ℂ} (hr : r ∈ L) (hrc : conj r ∈ L)
    (hr0 : r ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥L) t ∧ t * conj t = r * conj r
      ∧ t * conj t ∈ L := by
  refine ⟨r * Complex.exp Complex.I, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero hr0 (Complex.exp_ne_zero _)
  · intro hcon
    -- if `r·e^i` is algebraic over `L` then so is `e^i`, as `r ∈ L`
    refine transcendental_of_base (L := L) transcendental_exp_I ?_
    have : Complex.exp Complex.I = (r * Complex.exp Complex.I) * (r⁻¹) := by
      field_simp
    rw [this]
    exact hcon.mul (isAlgebraic_algebraMap (R := ↥L) ⟨r⁻¹, inv_mem hr⟩)
  · have hconj : conj (Complex.exp Complex.I) = Complex.exp (-Complex.I) := by
      rw [← Complex.exp_conj]; simp
    rw [map_mul, hconj]
    have : Complex.exp Complex.I * Complex.exp (-Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    calc r * Complex.exp Complex.I * (conj r * Complex.exp (-Complex.I))
        = (r * conj r) * (Complex.exp Complex.I * Complex.exp (-Complex.I)) := by ring
      _ = r * conj r := by rw [this, mul_one]
  · -- membership, which is where `conj r ∈ L` is needed
    have hconj : conj (Complex.exp Complex.I) = Complex.exp (-Complex.I) := by
      rw [← Complex.exp_conj]; simp
    have hone : Complex.exp Complex.I * Complex.exp (-Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [map_mul, hconj]
    have : r * Complex.exp Complex.I * (conj r * Complex.exp (-Complex.I))
        = r * conj r := by
      calc r * Complex.exp Complex.I * (conj r * Complex.exp (-Complex.I))
          = (r * conj r) * (Complex.exp Complex.I * Complex.exp (-Complex.I)) := by ring
        _ = r * conj r := by rw [hone, mul_one]
    rw [this]
    exact mul_mem hr hrc
end
