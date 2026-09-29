-- Prove2me | solution 1 for DiazModulus.geometric_triple_not_logs
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T16:24:17.389053+00:00
-- url     : https://prove2.me/submissions/24ed87bf-f436-4172-9c9c-426a3a514852

import Mathlib
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one

/-- If `w`, `wz` and `wz²` were all logarithms of algebraic numbers, the matrix
`[[w, wz], [wz, wz²]]` would have vanishing determinant, entries in a `ℚ`-algebra of
transcendence degree at most one, and neither rows nor columns `ℚ`-dependent unless `z` is
rational. -/
theorem solution (w z : ℂ) (hw : w ≠ 0) (hz : ∀ q : ℚ, z ≠ (q : ℂ))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({w, z} : Set ℂ)) ≤ 1) :
    ¬ (IsAlgebraic ℚ (Complex.exp w) ∧ IsAlgebraic ℚ (Complex.exp (w * z)) ∧
      IsAlgebraic ℚ (Complex.exp (w * z ^ 2))) := by
  rintro ⟨h1, h2, h3⟩
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hsub : Algebra.adjoin ℚ ({w, w * z, w * z, w * z ^ 2} : Set ℂ) ≤
      Algebra.adjoin ℚ ({w, z} : Set ℂ) := by
    rw [Algebra.adjoin_le_iff]
    have hwm : w ∈ Algebra.adjoin ℚ ({w, z} : Set ℂ) := Algebra.subset_adjoin (by simp)
    have hzm : z ∈ Algebra.adjoin ℚ ({w, z} : Set ℂ) := Algebra.subset_adjoin (by simp)
    rintro y (rfl | rfl | rfl | rfl)
    · exact hwm
    · exact Subalgebra.mul_mem _ hwm hzm
    · exact Subalgebra.mul_mem _ hwm hzm
    · exact Subalgebra.mul_mem _ hwm (Subalgebra.pow_mem _ hzm 2)
  have htr' : Algebra.trdeg ℚ
      ↥(Algebra.adjoin ℚ ({w, w * z, w * z, w * z ^ 2} : Set ℂ)) ≤ 1 :=
    (trdeg_le_of_injective (Subalgebra.inclusion hsub)
      (Subalgebra.inclusion_injective hsub)).trans htr
  have hwz : w * z ≠ 0 := mul_ne_zero hw hz0
  have key : ∀ p q : ℚ, ¬(p = 0 ∧ q = 0) → (p : ℂ) * w + (q : ℂ) * (w * z) = 0 → False := by
    intro p q hpq h
    have h' : w * ((p : ℂ) + (q : ℂ) * z) = 0 := by linear_combination h
    have hlin : (p : ℂ) + (q : ℂ) * z = 0 := (mul_eq_zero.1 h').resolve_left hw
    by_cases hq : q = 0
    · subst hq
      simp at hlin
      exact hpq ⟨by exact_mod_cast hlin, rfl⟩
    · have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
      refine hz (-p / q) ?_
      push_cast
      field_simp
      linear_combination hlin
  rcases DiazModulus.four_exponentials_trdeg_one w (w * z) (w * z) (w * z ^ 2)
      h1 h2 h2 h3 hw hwz hwz (mul_ne_zero hw (pow_ne_zero 2 hz0)) (by ring) htr' with
    ⟨p, q, hpq, e1, -⟩ | ⟨p, q, hpq, e1, -⟩
  · exact key p q hpq e1
  · exact key p q hpq e1

#print axioms solution
