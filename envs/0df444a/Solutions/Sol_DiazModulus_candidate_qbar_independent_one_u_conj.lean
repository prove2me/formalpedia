-- Prove2me | solution 1 for DiazModulus.candidate_qbar_independent_one_u_conj
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T11:44:22.082977+00:00
-- url     : https://prove2.me/submissions/f645cc1c-e291-411a-984a-c46cf3be58a8

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_Schanuel_baker_linear_forms_in_logarithms

open Complex ComplexConjugate

namespace R3_candidate_qbar_independent_one_u_conj

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem rho_eq (u : ℂ) : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

/-- A candidate lies on neither axis: there `ū = ±u`, so `u² = ±|u|²` would be algebraic, and so
would `u`, against Hermite–Lindemann. -/
theorem cand_off_axes {u : ℂ} (hu : DiazModulus.IsCandidate u) : u.im ≠ 0 ∧ u.re ≠ 0 := by
  obtain ⟨hu0, hnorm, hexp⟩ := hu
  have hρ : IsAlgebraic ℚ (u * conj u) := by rw [rho_eq]; exact hnorm.pow 2
  have key : ∀ s : ℂ, (s = 1 ∨ s = -1) → conj u = s * u → False := by
    intro s hs hc
    have hsq : IsAlgebraic ℚ (u ^ 2) := by
      rcases hs with rfl | rfl
      · rw [hc, one_mul] at hρ; rw [sq]; exact hρ
      · have : u ^ 2 = -(u * conj u) := by rw [hc]; ring
        rw [this]; exact hρ.neg
    exact DiazModulus.hermite_lindemann_holds u hu0 (hsq.of_pow (by norm_num)) hexp
  refine ⟨fun h => key 1 (Or.inl rfl) ?_, fun h => key (-1) (Or.inr rfl) ?_⟩
  · rw [one_mul]; exact Complex.conj_eq_iff_im.2 h
  · apply Complex.ext <;> simp [h]

/-- Real and imaginary parts of `a z + b z̄ = 0`. -/
theorem re_im_of_comb {a b : ℚ} {z : ℂ} (h : (a : ℂ) * z + (b : ℂ) * conj z = 0) :
    ((a : ℝ) + b) * z.re = 0 ∧ ((a : ℝ) - b) * z.im = 0 := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re,
    Complex.ratCast_im, Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.zero_im] at hr hi
  exact ⟨by linear_combination hr, by linear_combination hi⟩

/-- `u` and `ū` are `ℚ`-linearly independent: `s u + t ū = 0` gives `(s + t) Re u = 0` and
`(s - t) Im u = 0`, and `u` lies on neither axis. -/
theorem lin_indep {u : ℂ} (hu : DiazModulus.IsCandidate u) :
    LinearIndependent ℚ ![u, conj u] := by
  obtain ⟨him, hre⟩ := cand_off_axes hu
  refine LinearIndependent.pair_iff.2 fun s t hst => ?_
  rw [Rat.smul_def, Rat.smul_def] at hst
  obtain ⟨h1, h2⟩ := re_im_of_comb hst
  have hs1 : (s : ℝ) + t = 0 := (mul_eq_zero.1 h1).resolve_right hre
  have hs2 : (s : ℝ) - t = 0 := (mul_eq_zero.1 h2).resolve_right him
  exact ⟨by exact_mod_cast (by linarith : (s : ℝ) = 0),
    by exact_mod_cast (by linarith : (t : ℝ) = 0)⟩

end R3_candidate_qbar_independent_one_u_conj

open R3_candidate_qbar_independent_one_u_conj in
theorem solution (u : ℂ) (hu : DiazModulus.IsCandidate u) :
    ∀ p q : ℂ, IsAlgebraic ℚ p → IsAlgebraic ℚ q →
      IsAlgebraic ℚ (p * u + q * conj u) → p = 0 ∧ q = 0 := by
  intro p q hp hq hpq
  by_contra hne
  -- `u` and `ū` are logarithms of algebraic numbers
  have hexp : IsAlgebraic ℚ (Complex.exp u) := hu.2.2
  have hexpc : IsAlgebraic ℚ (Complex.exp (conj u)) := by
    rw [Complex.exp_conj]; exact hexp.algHom cjQ
  -- some coefficient of `b = (p, q)` is non-zero
  have hne' : -(p * u + q * conj u) ≠ 0 ∨ ∃ i, ![p, q] i ≠ 0 := by
    right
    by_cases hp0 : p = 0
    · exact ⟨1, by simpa using fun hq0 => hne ⟨hp0, hq0⟩⟩
    · exact ⟨0, by simpa using hp0⟩
  -- Baker with `b₀ = -(p u + q ū)`, `b = (p, q)`, `l = (u, ū)`: but `b₀ + p u + q ū = 0`
  refine Schanuel.baker_linear_forms_in_logarithms 2 ![u, conj u] (lin_indep hu) ?_
    (-(p * u + q * conj u)) ![p, q] hpq.neg ?_ hne' ?_
  · exact Fin.forall_fin_two.2 ⟨by simpa using hexp, by simpa using hexpc⟩
  · exact Fin.forall_fin_two.2 ⟨by simpa using hp, by simpa using hq⟩
  · simp [Fin.sum_univ_two]

#print axioms solution
