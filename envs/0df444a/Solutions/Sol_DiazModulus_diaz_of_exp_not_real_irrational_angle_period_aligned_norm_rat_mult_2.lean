-- Prove2me | solution 2 for DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_rat_mult
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:14:30.433274+00:00
-- url     : https://prove2.me/submissions/f2dfa381-7f24-4c4c-bc1d-20268b537071

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_candidate_nongeneric_four_exp_barrier

/-!
# The period-aligned `norm_rat_mult` half, from the non-generic four exponentials barrier

Suppose `exp u` is algebraic, so that `u` is a candidate. Write `s = Im u + rπ`, `β = πs` and
`X = πi`. The hypotheses say that `β` is algebraic and `‖u‖² = c₀β`, with `c₀ ≠ 0` since `u ≠ 0`.

* The matrix `[[u, si], [−c₀X, ū]]` has determinant `‖u‖² − c₀β = 0`, and its entries lie in
  `ℚu + ℚū + ℚX`, since `si = ½u − ½ū + rX`.
* `u` is algebraic over `ℚ[X]`, in four steps: `si = −β/X`, `i·Im u = si − rX`, `Re u`, whose
  square is `‖u‖² + (i·Im u)²`, and `u = Re u + i·Im u`.
* So `DiazModulus.candidate_nongeneric_four_exp_barrier` makes the rows or the columns
  `ℚ`-dependent. Neither can be: `Re u ≠ 0`, while `−c₀X` and `si` are non-zero and purely
  imaginary (`s ≠ 0` because `Im u ∉ ℚπ`).
-/

open Complex ComplexConjugate

namespace W5_norm_rat_mult

/-- A `ℚ`-relation `p u + q l = 0` with `Re u ≠ 0` and `l ≠ 0` purely imaginary is trivial. -/
theorem key {u l : ℂ} (hu : u.re ≠ 0) (hl : l.re = 0) (hl0 : l ≠ 0) {p q : ℚ}
    (h : (p : ℂ) * u + (q : ℂ) * l = 0) : p = 0 ∧ q = 0 := by
  have hp : p = 0 := by simpa [hl, hu] using congrArg Complex.re h
  subst hp
  exact ⟨rfl, by simpa [hl0] using h⟩

end W5_norm_rat_mult

open DiazModulus W5_norm_rat_mult in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) ∧
        ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) →
      Transcendental ℚ (Complex.exp u) := by
  rintro u hu0 hnorm - hax hirr - ⟨r, -, hβ, c₀, hc⟩ hexp
  set s : ℝ := u.im + (r : ℝ) * Real.pi with hs
  have hre : u.re ≠ 0 := fun h => hax (Or.inr h)
  have hs0 : s ≠ 0 := fun h => hirr ⟨-r, by push_cast; linarith⟩
  have hc₀ : c₀ ≠ 0 := by rintro rfl; simp [hu0] at hc
  have hX0 : ((Real.pi : ℝ) : ℂ) * I ≠ 0 := by simp [Real.pi_ne_zero]
  -- `u` is algebraic over `K = ℚ[πi]`
  have halg : IsAlgebraic (Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ)) u := by
    set K := Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ)
    have hQ (z : ℂ) (h : IsAlgebraic ℚ z) : IsAlgebraic K z :=
      h.extendScalars (algebraMap ℚ K).injective
    have hX : IsAlgebraic K (((Real.pi : ℝ) : ℂ) * I) :=
      isAlgebraic_algebraMap (⟨_, Algebra.subset_adjoin rfl⟩ : K)
    have hsI : IsAlgebraic K ((s : ℂ) * I) := by
      rw [show (s : ℂ) * I = -((Real.pi * s : ℝ) : ℂ) * (((Real.pi : ℝ) : ℂ) * I)⁻¹ by
        rw [eq_mul_inv_iff_mul_eq₀ hX0]; push_cast; linear_combination (s * Real.pi : ℂ) * I_sq]
      exact (hQ _ hβ).neg.mul hX.inv
    have hw : IsAlgebraic K ((u.im : ℂ) * I) := by
      rw [show (u.im : ℂ) * I = (s : ℂ) * I - (r : ℂ) * (((Real.pi : ℝ) : ℂ) * I) by
        rw [hs]; push_cast; ring]
      exact hsI.sub ((hQ _ (isAlgebraic_ratCast ℚ r)).mul hX)
    have hN : ((‖u‖ : ℝ) : ℂ) ^ 2 = (u.re : ℂ) ^ 2 + (u.im : ℂ) ^ 2 := by
      norm_cast; rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hRe : IsAlgebraic K (u.re : ℂ) := by
      refine IsAlgebraic.of_pow two_pos ?_
      rw [show (u.re : ℂ) ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 + ((u.im : ℂ) * I) ^ 2 by
        linear_combination -hN - (u.im : ℂ) ^ 2 * I_sq]
      exact ((hQ _ hnorm).pow 2).add (hw.pow 2)
    rw [← Complex.re_add_im u]
    exact hRe.add hw
  -- the matrix `[[u, si], [−c₀X, ū]]` over the basis `(u, ū, X)`, and its determinant
  have hν : (s : ℂ) * I = 2⁻¹ * u - 2⁻¹ * conj u + (r : ℂ) * (((Real.pi : ℝ) : ℂ) * I) := by
    have h := Complex.sub_conj u
    rw [hs]; push_cast at h ⊢; linear_combination (-2⁻¹ : ℂ) * h
  have hdet : u * conj u = (s : ℂ) * I * (-(c₀ : ℂ) * (((Real.pi : ℝ) : ℂ) * I)) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; push_cast
    linear_combination (c₀ * Real.pi * s : ℂ) * I_sq
  obtain ⟨p, q, hpq, h⟩ | ⟨p, q, hpq, h⟩ := candidate_nongeneric_four_exp_barrier u
    ⟨hu0, hnorm, hexp⟩ halg ![![![1, 0, 0], ![1 / 2, -1 / 2, r]], ![![0, 0, -c₀], ![0, 1, 0]]]
    ![![u, s * I], ![-c₀ * (((Real.pi : ℝ) : ℂ) * I), conj u]]
    (fun i j => by
      fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three]
      linear_combination hν)
    hdet
  · exact hpq (key hre (by simp) (by simp [hc₀, Real.pi_ne_zero]) (h 0))
  · exact hpq (key hre (by simp) (by simp [hs0]) (h 0))
