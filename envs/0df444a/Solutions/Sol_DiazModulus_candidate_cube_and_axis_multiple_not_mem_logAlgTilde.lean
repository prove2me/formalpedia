-- Prove2me | solution 1 for DiazModulus.candidate_cube_and_axis_multiple_not_mem_logAlgTilde
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T08:55:56.071727+00:00
-- url     : https://prove2.me/submissions/ca1cc4c1-4702-4424-9b64-ef1eba95af82

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_candidate_one_self_conj_linearIndependent
import Theorems.Thm_DiazModulus_diaz_2007_cor2_P_consequences
import Theorems.Thm_DiazModulus_diaz_2007_cor5

/-!
# A candidate's cube, and its products with a number on an axis

Under Roy's strong six exponentials theorem, for every candidate `u`:

* `u³ ∉ ℒ̃`. This is Corollaire 5(2) of G. Diaz (JTNB 19, 2007, p. 383) at `λ = u`, because
  `u²/ū = u³/|u|²`.
* `λu ∉ ℒ̃` for every transcendental `λ ∈ ℒ̃` on the real or the imaginary axis. This is Corollaire 2
  (P) 2) of the same paper (p. 381) at `λ₂ = u`, and Théorème 3(2) of Diaz (JTNB 16, 2004, p. 539) at
  `λ₁ = u`. Their hypothesis that `1, u, ū` are free over `Q̄` holds at a candidate by
  Hermite–Lindemann alone, so Baker's theorem is not needed here.
* In particular `πu ∉ ℒ̃`, so `e^{βπu}` is transcendental for every algebraic `β ≠ 0`.
-/

open Complex ComplexConjugate

namespace CandidateSSE

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

end CandidateSSE

open DiazModulus CandidateSSE in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) :
    u ^ 3 ∉ LogAlgTilde ∧
    (∀ l : ℂ, l ∈ LogAlgTilde → l ∉ Qbar → (l.im = 0 ∨ l.re = 0) → l * u ∉ LogAlgTilde) ∧
    (∀ β : ℂ, IsAlgebraic ℚ β → β ≠ 0 →
      Transcendental ℚ (Complex.exp (β * ((Real.pi : ℝ) : ℂ) * u))) := by
  have hu0 : u ≠ 0 := h.1
  have huT : u ∈ LogAlgTilde := mem_of_log h.2.2
  have huQ : u ∉ Qbar := fun hq => hermite_lindemann_holds u hu0 (mem_Qbar_iff.mp hq) h.2.2
  -- `1, u, ū` are free over `Q̄`
  have hfree : ∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * u + c * conj u = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c ha hb hc habc
    have hg := Fintype.linearIndependent_iff.mp (candidate_one_self_conj_linearIndependent h)
      ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩]
      (by rw [Fin.sum_univ_three]; show a * 1 + b * u + c * conj u = 0; rw [mul_one]; exact habc)
    exact ⟨congrArg Subtype.val (hg 0), congrArg Subtype.val (hg 1), congrArg Subtype.val (hg 2)⟩
  -- the axis part: Corollaire 2 (P) 2) at `λ₂ = u`
  have haxis : ∀ l : ℂ, l ∈ LogAlgTilde → l ∉ Qbar → (l.im = 0 ∨ l.re = 0) →
      l * u ∉ LogAlgTilde :=
    fun l hl hlQ hax => (diaz_2007_cor2_P_consequences hSSE).1 l u hl huT hax hlQ hfree
  refine ⟨?_, haxis, ?_⟩
  · -- the cube: Corollaire 5(2) at `λ = u`
    have hfree2 : ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * u + b * conj u = 0 → a = 0 ∧ b = 0 := by
      intro a b ha hb hab
      have := hfree 0 a b Qbar.zero_mem ha hb (by rw [zero_add]; exact hab)
      exact ⟨this.2.1, this.2.2⟩
    have h52 := (diaz_2007_cor5 hSSE huT huQ).2.1 hfree2
    have hρ : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have hρQ : (u * conj u)⁻¹ ∈ Qbar :=
      Qbar.inv_mem (hρ ▸ Qbar.pow_mem (mem_Qbar_iff.mpr h.2.1) 2)
    have hc0 : conj u ≠ 0 := (map_ne_zero _).mpr hu0
    intro h3
    apply h52
    have he : u ^ 2 / conj u = (u * conj u)⁻¹ * u ^ 3 := by field_simp
    rw [he]
    exact mul_mem hρQ h3
  · -- `e^{βπu}`: the axis part at `λ = π`
    intro β hβ hβ0 halg
    have hπT : ((Real.pi : ℝ) : ℂ) ∈ LogAlgTilde := by
      have h := mul_mem (Qbar.neg_mem I_mem) (mem_of_log piI_log)
      have he : -Complex.I * (((Real.pi : ℝ) : ℂ) * Complex.I) = ((Real.pi : ℝ) : ℂ) := by
        ring_nf; rw [Complex.I_sq]; ring
      rwa [he] at h
    have hπQ : ((Real.pi : ℝ) : ℂ) ∉ Qbar := by
      intro hq
      have hne : ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
      exact hermite_lindemann_holds _ hne (mem_Qbar_iff.mp (Qbar.mul_mem hq I_mem)) piI_log
    refine haxis _ hπT hπQ (Or.inl (Complex.ofReal_im _)) ?_
    have h := mem_of_log (z := β * ((Real.pi : ℝ) : ℂ) * u) halg
    rw [mul_assoc] at h
    exact of_mul_mem (mem_Qbar_iff.mpr hβ) hβ0 h
