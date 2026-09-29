-- Prove2me | solution 1 for DiazModulus.generic_conj_pair_no_quadratic_relation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T20:38:20.213101+00:00
-- url     : https://prove2.me/submissions/74406b6d-65bf-4fff-b12e-441cc5a4f185

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace GenConjNoQuad

open MvPolynomial

/-- The polynomial `a00 U⁴ + a02 U³Y + a22 U²Y² + a01 U² + a12 UY + a11` over `Q̄`. -/
noncomputable def P (a00 a02 a22 a01 a12 a11 : ↥DiazModulus.Qbar) :
    MvPolynomial (Fin 2) ↥DiazModulus.Qbar :=
  C a00 * X 0 ^ 4 + C a02 * X 0 ^ 3 * X 1 + C a22 * X 0 ^ 2 * X 1 ^ 2 + C a01 * X 0 ^ 2
    + C a12 * X 0 * X 1 + C a11

theorem aeval_P (a00 a02 a22 a01 a12 a11 : ↥DiazModulus.Qbar) (a b : ℂ) :
    aeval ![a, b] (P a00 a02 a22 a01 a12 a11) =
      (a00 : ℂ) * a ^ 4 + (a02 : ℂ) * a ^ 3 * b + (a22 : ℂ) * a ^ 2 * b ^ 2 + (a01 : ℂ) * a ^ 2
        + (a12 : ℂ) * a * b + (a11 : ℂ) := by
  simp [P]
  rfl

end GenConjNoQuad

open GenConjNoQuad in
theorem solution (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥DiazModulus.Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (F : Fin 3 → Fin 3 → ℚ)
    (h : ∑ k, ∑ l, (F k l : ℂ) * (![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] l) = 0) :
    ∀ k l, F k l + F l k = 0 := by
  have hρQ : u * conj u ∈ DiazModulus.Qbar := DiazModulus.mem_Qbar_iff.2 hρ
  have hρ0 : u * conj u ≠ 0 := mul_ne_zero hu ((map_ne_zero _).2 hu)
  set w : ℂ := ((Real.pi : ℝ) : ℂ) * Complex.I with hw
  set ρ : ℂ := u * conj u with hρdef
  let r : ↥DiazModulus.Qbar := ⟨ρ, hρQ⟩
  -- the symmetrised coefficients
  set s00 : ℚ := F 0 0 with hs00
  set s11 : ℚ := F 1 1 with hs11
  set s22 : ℚ := F 2 2 with hs22
  set s01 : ℚ := F 0 1 + F 1 0 with hs01
  set s02 : ℚ := F 0 2 + F 2 0 with hs02
  set s12 : ℚ := F 1 2 + F 2 1 with hs12
  let Pu : MvPolynomial (Fin 2) ↥DiazModulus.Qbar :=
    P (s00 : ↥DiazModulus.Qbar) (s02 : ↥DiazModulus.Qbar) (s22 : ↥DiazModulus.Qbar)
      ((s01 : ↥DiazModulus.Qbar) * r) ((s12 : ↥DiazModulus.Qbar) * r)
      ((s11 : ↥DiazModulus.Qbar) * r ^ 2)
  have hval : ∀ a b : ℂ, MvPolynomial.aeval ![a, b] Pu =
      (s00 : ℂ) * a ^ 4 + (s02 : ℂ) * a ^ 3 * b + (s22 : ℂ) * a ^ 2 * b ^ 2
        + (s01 : ℂ) * ρ * a ^ 2 + (s12 : ℂ) * ρ * a * b + (s11 : ℂ) * ρ ^ 2 := by
    intro a b
    simp only [Pu, aeval_P]
    push_cast
    rfl
  have h0 : MvPolynomial.aeval ![u, w] Pu = 0 := by
    rw [hval]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
    rw [hρdef, hs00, hs11, hs22, hs01, hs02, hs12]
    push_cast
    linear_combination u ^ 2 * h
  have hP : Pu = 0 := hgen.eq_zero_of_aeval_eq_zero Pu h0
  have ev : ∀ a b : ℂ, (s00 : ℂ) * a ^ 4 + (s02 : ℂ) * a ^ 3 * b + (s22 : ℂ) * a ^ 2 * b ^ 2
        + (s01 : ℂ) * ρ * a ^ 2 + (s12 : ℂ) * ρ * a * b + (s11 : ℂ) * ρ ^ 2 = 0 := by
    intro a b
    rw [← hval, hP, map_zero]
  have e00 := ev 0 0
  have e10 := ev 1 0
  have e20 := ev 2 0
  have e11 := ev 1 1
  have e1m := ev 1 (-1)
  have e21 := ev 2 1
  have h11 : (s11 : ℂ) = 0 := by
    have : (s11 : ℂ) * ρ ^ 2 = 0 := by linear_combination e00
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h) hρ0
  have h00 : (s00 : ℂ) = 0 := by
    linear_combination (-(1 : ℂ) / 3) * e10 + (1 / 12 : ℂ) * e20 + (1 / 4 : ℂ) * ρ ^ 2 * h11
  have h01 : (s01 : ℂ) = 0 := by
    have : (s01 : ℂ) * ρ = 0 := by
      linear_combination e10 - ρ ^ 2 * h11 - h00
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hρ0
  have h22 : (s22 : ℂ) = 0 := by
    linear_combination (1 / 2 : ℂ) * e11 + (1 / 2 : ℂ) * e1m - h00 - ρ * h01 - ρ ^ 2 * h11
  have h02 : (s02 : ℂ) = 0 := by
    linear_combination (1 / 6 : ℂ) * e21 - (1 / 6 : ℂ) * e11 + (1 / 6 : ℂ) * e1m
      - (16 / 6 : ℂ) * h00 - (4 / 6 : ℂ) * h22 - (4 / 6 : ℂ) * ρ * h01
      - (1 / 6 : ℂ) * ρ ^ 2 * h11
  have h12 : (s12 : ℂ) = 0 := by
    have : (s12 : ℂ) * ρ = 0 := by
      linear_combination (1 / 2 : ℂ) * e11 - (1 / 2 : ℂ) * e1m - h02
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hρ0
  have q00 : s00 = 0 := by exact_mod_cast h00
  have q11 : s11 = 0 := by exact_mod_cast h11
  have q22 : s22 = 0 := by exact_mod_cast h22
  have q01 : s01 = 0 := by exact_mod_cast h01
  have q02 : s02 = 0 := by exact_mod_cast h02
  have q12 : s12 = 0 := by exact_mod_cast h12
  intro k l
  fin_cases k <;> fin_cases l <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Fin.isValue] <;> linarith

#print axioms solution
