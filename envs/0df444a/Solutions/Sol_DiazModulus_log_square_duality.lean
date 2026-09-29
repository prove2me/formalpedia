-- Prove2me | solution 1 for DiazModulus.log_square_duality
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:25:03.128686+00:00
-- url     : https://prove2.me/submissions/0c62b199-0228-4065-97ad-cc6bb7d387ba

import Mathlib
import Theorems.Thm_DiazModulus_six_exponentials
import Theorems.Thm_Schanuel_gelfond_schneider

namespace LogSqDuality

/-- If `z` is transcendental and `b z² + a z + c = 0` with `a, b, c` rational, then
`a = b = c = 0`. -/
theorem quad_zero {z : ℂ} (hz : Transcendental ℚ z) (a b c : ℚ)
    (h : (b : ℂ) * z ^ 2 + (a : ℂ) * z + (c : ℂ) = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hP : (Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X +
      Polynomial.C c : Polynomial ℚ) = 0 := by
    by_contra hne
    refine hz ⟨_, hne, ?_⟩
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      eq_ratCast]
    exact h
  have e2 := congrArg (fun P : Polynomial ℚ => P.coeff 2) hP
  have e1 := congrArg (fun P : Polynomial ℚ => P.coeff 1) hP
  have e0 := congrArg (fun P : Polynomial ℚ => P.coeff 0) hP
  simp [Polynomial.coeff_X, Polynomial.coeff_C] at e2 e1 e0
  exact ⟨e1, e2, e0⟩

end LogSqDuality

open LogSqDuality in
/-- Six exponentials at `x = (1, z)`, `y = (m, l, m²/l)` with `z = l/m`: the six products are
`m, l, m²/l, l, l²/m, m`. -/
theorem solution (l m : ℂ) (hl : IsAlgebraic ℚ (Complex.exp l))
    (hm : IsAlgebraic ℚ (Complex.exp m)) (hind : LinearIndependent ℚ ![l, m]) :
    Transcendental ℚ (Complex.exp (l ^ 2 / m)) ∨ Transcendental ℚ (Complex.exp (m ^ 2 / l)) := by
  by_contra hcon
  simp only [not_or, Transcendental, not_not] at hcon
  obtain ⟨hA, hB⟩ := hcon
  rw [LinearIndependent.pair_iff] at hind
  have hl0 : l ≠ 0 := by
    intro h0
    have := hind 1 0 (by simp [h0])
    exact one_ne_zero this.1
  have hm0 : m ≠ 0 := by
    intro h0
    have := hind 0 1 (by simp [h0])
    exact one_ne_zero this.2
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = l / m := ⟨_, rfl⟩
  have hzm : z * m = l := by rw [hz]; field_simp
  -- `z ∉ ℚ`
  have hzq : ∀ q : ℚ, z ≠ (q : ℂ) := by
    intro q hq
    have := hind 1 (-q) (by
      rw [Rat.smul_def, Rat.smul_def, ← hzm, hq]
      push_cast
      ring)
    exact one_ne_zero this.1
  -- `z` is transcendental, by Gelfond–Schneider
  have hztr : Transcendental ℚ z := by
    intro hzalg
    have := Schanuel.gelfond_schneider z m hzalg hzq hm hm0
    rw [hzm] at this
    exact this hl
  -- `x = (1, z)` is `ℚ`-independent
  have hx : LinearIndependent ℚ ![(1 : ℂ), z] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Rat.smul_def, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      refine hzq (-s / t) ?_
      push_cast
      field_simp
      linear_combination hst
  -- `y = (m, l, m²/l)` is `ℚ`-independent
  have hy : LinearIndependent ℚ ![m, l, m ^ 2 / l] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Rat.smul_def] at hg
    have e : (g 2 : ℂ) * (m ^ 2 / l) * l = (g 2 : ℂ) * m ^ 2 := by field_simp
    have hg' : (g 0 : ℂ) * m * l + (g 1 : ℂ) * l ^ 2 + (g 2 : ℂ) * m ^ 2 = 0 := by
      linear_combination l * hg - e
    have hpoly : (g 1 : ℂ) * z ^ 2 + (g 0 : ℂ) * z + (g 2 : ℂ) = 0 := by
      have : (g 1 : ℂ) * z ^ 2 + (g 0 : ℂ) * z + (g 2 : ℂ) =
          ((g 0 : ℂ) * m * l + (g 1 : ℂ) * l ^ 2 + (g 2 : ℂ) * m ^ 2) / m ^ 2 := by
        rw [hz]; field_simp; ring
      rw [this, hg', zero_div]
    obtain ⟨h0, h1, h2⟩ := quad_zero hztr (g 0) (g 1) (g 2) hpoly
    intro i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hall : ∀ i j,
      IsAlgebraic ℚ (Complex.exp (![(1 : ℂ), z] i * ![m, l, m ^ 2 / l] j)) := by
    intro i j
    fin_cases i <;> fin_cases j
    · change IsAlgebraic ℚ (Complex.exp (1 * m)); rw [one_mul]; exact hm
    · change IsAlgebraic ℚ (Complex.exp (1 * l)); rw [one_mul]; exact hl
    · change IsAlgebraic ℚ (Complex.exp (1 * (m ^ 2 / l))); rw [one_mul]; exact hB
    · change IsAlgebraic ℚ (Complex.exp (z * m)); rw [hzm]; exact hl
    · change IsAlgebraic ℚ (Complex.exp (z * l))
      rw [show z * l = l ^ 2 / m by rw [hz]; ring]; exact hA
    · change IsAlgebraic ℚ (Complex.exp (z * (m ^ 2 / l)))
      rw [show z * (m ^ 2 / l) = m by rw [hz]; field_simp]; exact hm
  obtain ⟨i, j, hij⟩ := DiazModulus.six_exponentials _ _ hx hy
  exact hij (hall i j)

#print axioms solution
