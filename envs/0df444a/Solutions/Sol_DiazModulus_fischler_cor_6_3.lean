-- Prove2me | solution 1 for DiazModulus.fischler_cor_6_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:18:50.756577+00:00
-- url     : https://prove2.me/submissions/a5c33b06-dc48-4fe3-9bb0-beb1efcb684b

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fischler_theorem_1_1

open Complex ComplexConjugate

/-! # Fischler 2001, Corollary 6.3 (1)

Let `P = Λᵏ` with `k ≥ 3` and every coefficient in `ℒ̃`. By Fischler's Theorem 1.1, `P = aφᵏ` with `a ∈ ℒ̃` and
`φ = Σᵢ φᵢXᵢ` a linear form with algebraic coefficients. Take `Q = φᵏ`. Its coefficients are algebraic, since `Q`
is the image of a polynomial with coefficients in `Q̄` under the inclusion `Q̄ → ℂ`. `P = aQ` lies on the line
`ℂQ`. Every point of that line is a `k`-th power of a linear form: given `γQ`, choose `z` with `zᵏ = γ` (`ℂ` is
algebraically closed); then `γQ = (zφ)ᵏ = (Σᵢ zφᵢXᵢ)ᵏ`. -/

open DiazModulus MvPolynomial in
theorem solution {m k : ℕ} (hk : 3 ≤ k) (P : MvPolynomial (Fin m) ℂ)
    (hP : ∀ s, P.coeff s ∈ LogAlgTilde) (Λ : Fin m → ℂ)
    (hPΛ : P = (∑ i, MvPolynomial.C (Λ i) * MvPolynomial.X i) ^ k) :
    ∃ Q : MvPolynomial (Fin m) ℂ, (∀ s, Q.coeff s ∈ Qbar) ∧ P ∈ Submodule.span ℂ {Q} ∧
      ∀ R ∈ Submodule.span ℂ {Q}, ∃ Λ' : Fin m → ℂ,
        R = (∑ i, MvPolynomial.C (Λ' i) * MvPolynomial.X i) ^ k := by
  obtain ⟨φ, hφ, a, -, hPa⟩ := DiazModulus.fischler_theorem_1_1 hk P hP Λ hPΛ
  refine ⟨(∑ i, C (φ i) * X i) ^ k, fun s => ?_, ?_, fun R hR => ?_⟩
  · have hmap : (∑ i, C (φ i) * X i : MvPolynomial (Fin m) ℂ) ^ k =
        MvPolynomial.map Qbar.subtype ((∑ i, C (⟨φ i, hφ i⟩ : ↥Qbar) * X i) ^ k) := by
      simp [map_pow, map_sum]
    rw [hmap, MvPolynomial.coeff_map]
    exact SetLike.coe_mem _
  · rw [hPa, Submodule.mem_span_singleton]
    exact ⟨a, C_mul'.symm⟩
  · obtain ⟨γ, rfl⟩ := Submodule.mem_span_singleton.1 hR
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq γ (show 0 < k by omega)
    refine ⟨fun i => z * φ i, ?_⟩
    have hL : (∑ i, C (z * φ i) * X i : MvPolynomial (Fin m) ℂ) = C z * ∑ i, C (φ i) * X i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [C_mul, mul_assoc]
    rw [hL, mul_pow, ← C_pow, hz, C_mul']
