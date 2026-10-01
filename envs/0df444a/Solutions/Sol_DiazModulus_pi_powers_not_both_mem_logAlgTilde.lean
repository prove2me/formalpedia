-- Prove2me | solution 1 for DiazModulus.pi_powers_not_both_mem_logAlgTilde
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T08:55:58.719824+00:00
-- url     : https://prove2.me/submissions/af7a8608-d6a1-4956-a478-0635192409a3

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_diaz_2007_cor1_PQ
import Theorems.Thm_DiazModulus_diaz_2007_cor2_P_consequences

/-!
# Powers of `π` outside `ℒ̃`, under the strong six exponentials theorem

G. Diaz (JTNB 19, 2007) applies his results at `λ = iπ` himself: Corollaire 1 (PQ) 3) and 4) give
that `exp(π²)` or `exp(1/π)` is transcendental, and that `exp(1/π)` or `exp(1/π²)` is (p. 380);
Conséquence 3 of Corollaire 2 (P) gives that `exp(απ²)` or `exp(βπ³)` is transcendental (p. 381).
This file records the three statements in their `ℒ̃` form, and one reading of them.

If the statement (S) fails, that is, `e^{γ/(πi)}` is algebraic for some algebraic `γ ≠ 0`, then
`1/π ∈ ℒ̃`, and the first two pairs force `π² ∉ ℒ̃` and `1/π² ∉ ℒ̃`.
-/

open Complex ComplexConjugate

namespace PiPowers

open DiazModulus

theorem mem_of_log {z : ℂ} (h : z ∈ LogAlg) : z ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert_of_mem _ h)

theorem mul_mem {c z : ℂ} (hc : c ∈ Qbar) (hz : z ∈ LogAlgTilde) : c * z ∈ LogAlgTilde :=
  Submodule.smul_mem LogAlgTilde (⟨c, hc⟩ : ↥Qbar) hz

theorem of_mul_mem {c z : ℂ} (hc : c ∈ Qbar) (hc0 : c ≠ 0) (h : c * z ∈ LogAlgTilde) :
    z ∈ LogAlgTilde := by
  have := mul_mem (Qbar.inv_mem hc) h
  rwa [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at this

theorem I_mem : Complex.I ∈ Qbar :=
  mem_Qbar_iff.mpr ⟨Polynomial.X ^ 2 + Polynomial.C 1,
    (Polynomial.monic_X_pow_add_C 1 two_ne_zero).ne_zero, by simp⟩

theorem piI_log : ((Real.pi : ℝ) : ℂ) * Complex.I ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I))
  rw [Complex.exp_pi_mul_I]
  exact (isAlgebraic_one).neg

theorem piI_not_mem : ((Real.pi : ℝ) : ℂ) * Complex.I ∉ Qbar := by
  intro h
  have hne : ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
  exact hermite_lindemann_holds _ hne (mem_Qbar_iff.mp h) piI_log

end PiPowers

open DiazModulus PiPowers in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    ¬ (((Real.pi : ℝ) : ℂ) ^ 2 ∈ LogAlgTilde ∧ ((Real.pi : ℝ) : ℂ) ^ 3 ∈ LogAlgTilde) ∧
    ¬ (((Real.pi : ℝ) : ℂ) ^ 2 ∈ LogAlgTilde ∧ 1 / ((Real.pi : ℝ) : ℂ) ∈ LogAlgTilde) ∧
    ¬ (1 / ((Real.pi : ℝ) : ℂ) ∈ LogAlgTilde ∧ 1 / ((Real.pi : ℝ) : ℂ) ^ 2 ∈ LogAlgTilde) ∧
    (∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      ∀ β : ℂ, IsAlgebraic ℚ β → β ≠ 0 →
        Transcendental ℚ (Complex.exp (β * ((Real.pi : ℝ) : ℂ) ^ 2)) ∧
        Transcendental ℚ (Complex.exp (β / ((Real.pi : ℝ) : ℂ) ^ 2))) := by
  set π' : ℂ := ((Real.pi : ℝ) : ℂ) with hπ'
  have hπ0 : π' ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΛ : π' * Complex.I ∈ LogAlgTilde := mem_of_log piI_log
  have hΛQ : π' * Complex.I ∉ Qbar := piI_not_mem
  have hm1 : (-1 : ℂ) ∈ Qbar := Qbar.neg_mem Qbar.one_mem
  have hmI : -Complex.I ∈ Qbar := Qbar.neg_mem I_mem
  have hsq : (π' * Complex.I) ^ 2 = -1 * π' ^ 2 := by ring_nf; rw [Complex.I_sq]; ring
  have hcube : (π' * Complex.I) ^ 3 = -Complex.I * π' ^ 3 := by
    ring_nf; rw [Complex.I_pow_three]; ring
  have hrec : 1 / (π' * Complex.I) = -Complex.I * (1 / π') := by
    field_simp; rw [Complex.I_sq]; ring
  have hrec2 : 1 / (π' * Complex.I) ^ 2 = -1 * (1 / π' ^ 2) := by
    rw [hsq]; field_simp
  obtain ⟨-, -, -, h3, -, h4⟩ := diaz_2007_cor1_PQ hSSE
  obtain ⟨-, -, -, c3⟩ := diaz_2007_cor2_P_consequences hSSE
  have p1 : ¬ (π' ^ 2 ∈ LogAlgTilde ∧ π' ^ 3 ∈ LogAlgTilde) := by
    rintro ⟨h2, h3'⟩
    refine c3 _ hΛ hΛQ ⟨?_, ?_⟩
    · rw [hsq]; exact mul_mem hm1 h2
    · rw [hcube]; exact mul_mem hmI h3'
  have p2 : ¬ (π' ^ 2 ∈ LogAlgTilde ∧ 1 / π' ∈ LogAlgTilde) := by
    rintro ⟨h2, hr⟩
    refine h3 _ hΛ hΛQ ⟨?_, ?_⟩
    · rw [hsq]; exact mul_mem hm1 h2
    · rw [hrec]; exact mul_mem hmI hr
  have p3 : ¬ (1 / π' ∈ LogAlgTilde ∧ 1 / π' ^ 2 ∈ LogAlgTilde) := by
    rintro ⟨hr, hr2⟩
    refine h4 _ hΛ hΛQ ⟨?_, ?_⟩
    · rw [hrec]; exact mul_mem hmI hr
    · rw [hrec2]; exact mul_mem hm1 hr2
  refine ⟨p1, p2, p3, ?_⟩
  intro γ hγ hγ0 hS β hβ hβ0
  -- an exception to (S) puts `1/π` in `ℒ̃`
  have hγQ : γ ∈ Qbar := mem_Qbar_iff.mpr hγ
  have hr : 1 / π' ∈ LogAlgTilde := by
    have hc : Complex.I * γ⁻¹ ∈ Qbar := Qbar.mul_mem I_mem (Qbar.inv_mem hγQ)
    have h := mul_mem hc (mem_of_log (z := γ / (π' * Complex.I)) hS)
    have he : Complex.I * γ⁻¹ * (γ / (π' * Complex.I)) = 1 / π' := by
      field_simp
    rwa [he] at h
  have hβQ : β ∈ Qbar := mem_Qbar_iff.mpr hβ
  refine ⟨fun hb => p2 ⟨?_, hr⟩, fun hb => p3 ⟨hr, ?_⟩⟩
  · exact of_mul_mem hβQ hβ0 (mem_of_log hb)
  · have h := mem_of_log (z := β / π' ^ 2) hb
    rw [div_eq_mul_one_div] at h
    exact of_mul_mem hβQ hβ0 h
