-- Prove2me | solution 1 for DiazModulus.candidate_one_log_saturation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T09:45:15.311767+00:00
-- url     : https://prove2.me/submissions/8b9adfc3-f8bb-44c4-bf2d-e9e8119f0c90

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_pi_transcendental

open Complex ComplexConjugate

open DiazModulus in
theorem solution
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y))
    (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u) :
    (∀ l : ℂ, l ∈ LogAlg → ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar →
        u = a + b * l → ∃ r : ℚ, u = (r : ℂ) * l)
      ∧ (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → u ≠ a + b * ((Real.pi : ℝ) : ℂ)) := by
  obtain ⟨hu, hnorm, hexp⟩ := h
  have huQ : u ∉ Qbar := fun hq => hHL u hu (mem_Qbar_iff.mp hq) hexp
  have sat : ∀ l : ℂ, l ∈ LogAlg → ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar →
      u = a + b * l → ∃ r : ℚ, u = (r : ℂ) * l := by
    intro l hl a b haQ hbQ heq
    by_cases hdep : ∀ p q : ℚ, (p : ℂ) * u + (q : ℂ) * l = 0 → p = 0 ∧ q = 0
    · -- `u` and `l` are `ℚ`-independent: Baker contradicts `u - b*l = a`
      have hT := hB u l 1 (-b) hexp hl hdep isAlgebraic_one
        (mem_Qbar_iff.mp (Subfield.neg_mem _ hbQ)) (by simp)
      have hval : (1 : ℂ) * u + (-b) * l = a := by rw [heq]; ring
      rw [hval] at hT
      exact absurd (mem_Qbar_iff.mp haQ) hT
    · -- dependent: `u` is a rational multiple of `l`
      push_neg at hdep
      obtain ⟨p, q, hpq, hne⟩ := hdep
      have hp : p ≠ 0 := by
        intro hp0
        rw [hp0] at hpq
        simp only [Rat.cast_zero, zero_mul, zero_add] at hpq
        rcases mul_eq_zero.mp hpq with hq0 | hl0
        · exact hne hp0 (by exact_mod_cast hq0)
        · refine absurd ?_ huQ
          rw [heq, hl0]
          simpa using haQ
      refine ⟨-q / p, ?_⟩
      have hpc : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp
      push_cast
      field_simp
      linear_combination hpq
  refine ⟨sat, ?_⟩
  -- the instance `l = iπ`: no candidate has the form `a + bπ`
  intro a b haQ hbQ heq
  have hIpi : (((Real.pi : ℝ) : ℂ) * Complex.I) ∈ LogAlg := by
    have hval : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
    show IsAlgebraic ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I))
    rw [hval]
    exact isAlgebraic_one.neg
  have hIQ : Complex.I ∈ Qbar := by
    refine mem_Qbar_iff.mpr ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
    · intro hc
      have h0 : (Polynomial.X ^ 2 + 1 : Polynomial ℚ).coeff 0 = 1 := by simp
      rw [hc] at h0; simp at h0
    · simp [Complex.I_sq]
  have hbIQ : (-Complex.I * b) ∈ Qbar :=
    Subfield.mul_mem _ (Subfield.neg_mem _ hIQ) hbQ
  obtain ⟨r, hr⟩ := sat _ hIpi a (-Complex.I * b) haQ hbIQ (by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    rw [heq]
    linear_combination (b * ((Real.pi : ℝ) : ℂ)) * hI)
  have hrne : r ≠ 0 := by
    intro h0
    rw [h0] at hr
    simp at hr
    exact hu hr
  have hnormu : ((‖u‖ : ℝ) : ℂ) = ((|r| : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ) := by
    rw [hr]
    simp [abs_of_pos Real.pi_pos]
    norm_cast
  have habs : ((|r| : ℚ) : ℂ) ≠ 0 := by
    simp [abs_eq_zero, hrne]
  have hpiQ : ((Real.pi : ℝ) : ℂ) ∈ Qbar := by
    have h1 : ((‖u‖ : ℝ) : ℂ) ∈ Qbar := mem_Qbar_iff.mpr hnorm
    have h2 : ((Real.pi : ℝ) : ℂ) = ((‖u‖ : ℝ) : ℂ) / ((|r| : ℚ) : ℂ) := by
      rw [hnormu]; field_simp
    rw [h2]
    exact Subfield.div_mem _ h1 (mem_Qbar_iff.mpr (isAlgebraic_ratCast ℚ |r|))
  exact pi_transcendental (mem_Qbar_iff.mp hpiQ)
