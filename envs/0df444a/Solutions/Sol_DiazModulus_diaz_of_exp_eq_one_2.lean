-- Prove2me | solution 2 for DiazModulus.diaz_of_exp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @curiyu
-- created : 2026-09-08T04:37:42.225527+00:00
-- url     : https://prove2.me/submissions/ca55ae97-e450-428b-bc7d-c3b02e6a8b32

import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_pi_transcendental

open Complex ComplexConjugate

open DiazModulus in
theorem solution : ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) →
    (Complex.exp u).im = 0 → u.im ≠ 0 → Complex.exp u = 1 →
    Transcendental ℚ (Complex.exp u) := by
  intro u hu halg him1 him2 heq
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp heq
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    simp at hn
    exact hu hn
  have h2norm : ‖((2 * ((Real.pi : ℝ) : ℂ) * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    rw [show ((2 * ((Real.pi : ℝ) : ℂ) * Complex.I) : ℂ)
        = (2 : ℂ) * (((Real.pi : ℝ) : ℂ)) * Complex.I by ring]
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_two,
      Complex.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  have habs : |((n : ℤ) : ℝ)| = ((n.natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
  have hnorm : ‖u‖ = ((n.natAbs : ℕ) : ℝ) * (2 * Real.pi) := by
    have h1 : ‖u‖ = |((n : ℤ) : ℝ)| * (2 * Real.pi) := by
      rw [hn, Complex.norm_mul, Complex.norm_intCast, h2norm]
    rw [habs] at h1
    exact h1
  have hnatAbs_ne : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn0
  have hnatR_ne : ((n.natAbs : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnatAbs_ne
  have hDenR_ne : (2 : ℝ) * ((n.natAbs : ℕ) : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) hnatR_ne
  have hpi_eq : Real.pi = ‖u‖ / (2 * ((n.natAbs : ℕ) : ℝ)) := by
    rw [hnorm]
    field_simp
  have hNormMem : ((‖u‖ : ℝ) : ℂ) ∈ Qbar := mem_Qbar_iff.mpr halg
  have h2mem : (2 : ℂ) ∈ Qbar := by
    have h : IsAlgebraic ℚ (((2 : ℕ) : ℂ)) := isAlgebraic_natCast 2
    norm_cast at h ⊢
    exact mem_Qbar_iff.mpr h
  have hnatmem : ((((n.natAbs : ℕ)) : ℂ)) ∈ Qbar :=
    mem_Qbar_iff.mpr (isAlgebraic_natCast _)
  have hDenMem : ((((2 * ((n.natAbs : ℕ) : ℝ) : ℝ)) : ℂ)) ∈ Qbar := by
    have heq2 : ((((2 * ((n.natAbs : ℕ) : ℝ) : ℝ)) : ℂ))
        = (2 : ℂ) * ((((n.natAbs : ℕ)) : ℂ)) := by
      push_cast
      ring
    rw [heq2]
    exact Qbar.mul_mem h2mem hnatmem
  have hEq : ((((Real.pi : ℝ)) : ℂ))
      = ((‖u‖ : ℝ) : ℂ) / ((((2 * ((n.natAbs : ℕ) : ℝ) : ℝ)) : ℂ)) := by
    rw [hpi_eq, Complex.ofReal_div]
  have hPiMem : ((((Real.pi : ℝ)) : ℂ)) ∈ Qbar := by
    rw [hEq]
    exact Qbar.div_mem hNormMem hDenMem
  have hPiAlg : IsAlgebraic ℚ ((((Real.pi : ℝ)) : ℂ)) := mem_Qbar_iff.mp hPiMem
  have hFalse : False := pi_transcendental hPiAlg
  exact False.elim hFalse
