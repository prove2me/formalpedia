-- Prove2me | solution 1 for DiazModulus.no_algebraic_generalized_line
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-09T15:03:15.87367+00:00
-- url     : https://prove2.me/submissions/4e2d5085-4977-4578-a9ff-8b0cac75b12b

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazLine
open DiazModulus

/-- Baker's theorem in the form used here: a non-zero `Q̄`-linear combination of two
`ℚ`-linearly independent logarithms of algebraic numbers is transcendental. Carried as an
explicit hypothesis; it is a theorem, but not available formally in this environment. -/
def BakerTwoLogs : Prop :=
  ∀ x y a b : ℂ,
    IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
    (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
    IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
    Transcendental ℚ (a * x + b * y)

/-- Off both axes, `λ` and `conj λ` are `ℚ`-linearly independent. -/
theorem indep_of_off_axes {l : ℂ} (hre : l.re ≠ 0) (him : l.im ≠ 0) :
    ∀ p q : ℚ, (p : ℂ) * l + (q : ℂ) * conj l = 0 → p = 0 ∧ q = 0 := by
  intro p q h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.zero_re, Complex.zero_im, zero_mul, mul_zero, sub_zero, add_zero,
    zero_add, zero_sub] at hr hi
  have hre' : ((p : ℝ) + (q : ℝ)) * l.re = 0 := by linarith [hr]
  have him' : ((p : ℝ) - (q : ℝ)) * l.im = 0 := by linarith [hi]
  have h1 : (p : ℝ) + (q : ℝ) = 0 := by
    rcases mul_eq_zero.mp hre' with h | h
    · exact h
    · exact absurd h hre
  have h2 : (p : ℝ) - (q : ℝ) = 0 := by
    rcases mul_eq_zero.mp him' with h | h
    · exact h
    · exact absurd h him
  have hp : (p : ℝ) = 0 := by linarith
  have hq : (q : ℝ) = 0 := by linarith
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hq⟩

/-- **No algebraic generalized line.** A logarithm of an algebraic number lying off both
coordinate axes satisfies no Hermitian linear relation `Bλ + conj B · conj λ + C = 0` with
`B` algebraic non-zero and `C` algebraic real. Hence, within the conjugation-degree-one
stratum, its canonical curve is a genuine circle and never a line. -/
theorem no_algebraic_line (hB : BakerTwoLogs)
    {l : ℂ} (hlog : IsAlgebraic ℚ (Complex.exp l))
    (hre : l.re ≠ 0) (him : l.im ≠ 0)
    {B C : ℂ} (hBalg : IsAlgebraic ℚ B) (hB0 : B ≠ 0)
    (hCalg : IsAlgebraic ℚ C) :
    B * l + conj B * conj l + C ≠ 0 := by
  intro hrel
  -- `conj l` is also a logarithm of an algebraic number
  have hlogc : IsAlgebraic ℚ (Complex.exp (conj l)) := by
    rw [Complex.exp_conj]
    obtain ⟨p, hp0, hp⟩ := hlog
    refine ⟨p, hp0, ?_⟩
    have hcj : ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ) (Complex.exp l)
        = conj (Complex.exp l) := rfl
    have := Polynomial.aeval_algHom_apply
      ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ) (Complex.exp l) p
    rw [hcj] at this
    rw [this, hp, map_zero]
  -- `conj B` is algebraic
  have hBcalg : IsAlgebraic ℚ (conj B) := by
    obtain ⟨p, hp0, hp⟩ := hBalg
    refine ⟨p, hp0, ?_⟩
    have hcj : ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ) B = conj B := rfl
    have := Polynomial.aeval_algHom_apply
      ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ) B p
    rw [hcj] at this
    rw [this, hp, map_zero]
  -- Baker: the combination is transcendental
  have htr : Transcendental ℚ (B * l + conj B * conj l) :=
    hB l (conj l) B (conj B) hlog hlogc (indep_of_off_axes hre him) hBalg hBcalg
      (fun h => hB0 h.1)
  -- but the relation makes it equal to `-C`, which is algebraic
  refine htr ?_
  have : B * l + conj B * conj l = -C := by linear_combination hrel
  rw [this]
  exact (IsAlgebraic.neg hCalg)

end DiazLine


open DiazModulus in
theorem solution :
    (∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y)) →
    ∀ l : ℂ, IsAlgebraic ℚ (Complex.exp l) → l.re ≠ 0 → l.im ≠ 0 →
      ∀ B C : ℂ, IsAlgebraic ℚ B → B ≠ 0 → IsAlgebraic ℚ C →
        B * l + (starRingEnd ℂ) B * (starRingEnd ℂ) l + C ≠ 0 :=
  fun hB l hlog hre him B C hBalg hB0 hCalg =>
    DiazLine.no_algebraic_line hB hlog hre him hBalg hB0 hCalg
