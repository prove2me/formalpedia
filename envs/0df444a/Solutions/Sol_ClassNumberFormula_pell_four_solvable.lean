-- Prove2me | solution 1 for ClassNumberFormula.pell_four_solvable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:30:48.954189+00:00
-- url     : https://prove2.me/submissions/c381e9a4-99f6-46d6-9b89-658b613db732

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker

namespace CNPell
open ClassNumberFormula

lemma sq_squarefree {k : ℤ} (h : Squarefree (k * k)) : IsUnit k := h k dvd_rfl

lemma not_isSquare (d : ℤ) (hd : IsFundamentalDiscriminant d) (hpos : 0 < d) : ¬ IsSquare d := by
  rintro ⟨k, rfl⟩
  obtain ⟨h1, h2 | ⟨m, hm, hm4, hmsq⟩⟩ := hd
  · have hu := sq_squarefree h2.2
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp at h1
  · -- 4m = k*k ⇒ k even ⇒ m = (k/2)^2
    have hk2 : 2 ∣ k := by
      have : (2 : ℤ) ∣ k * k := ⟨2 * m, by rw [hm]; ring⟩
      exact (Int.prime_two.dvd_mul.mp this).elim id id
    obtain ⟨j, rfl⟩ := hk2
    have hmj : m = j * j := by linarith
    rw [hmj] at hmsq hm4
    have hu := sq_squarefree hmsq
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> norm_num at hm4

theorem main (d : ℤ) (hd : IsFundamentalDiscriminant d) (hpos : 0 < d) :
    ∃ t u : ℕ, 0 < t ∧ 0 < u ∧ (t : ℤ) ^ 2 - d * (u : ℤ) ^ 2 = 4 := by
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare hpos (not_isSquare d hd hpos)
  have hx : x ≠ 0 := by
    rintro rfl
    have : 0 ≤ d * y ^ 2 := by positivity
    linarith
  refine ⟨2 * x.natAbs, 2 * y.natAbs, by positivity, by positivity, ?_⟩
  push_cast
  have h1 : |x| ^ 2 = x ^ 2 := sq_abs x
  have h2 : |y| ^ 2 = y ^ 2 := sq_abs y
  nlinarith [h1, h2]

end CNPell

open ClassNumberFormula in
theorem solution (d : ℤ) (hd : IsFundamentalDiscriminant d) (hpos : 0 < d) :
    ∃ t u : ℕ, 0 < t ∧ 0 < u ∧ (t : ℤ) ^ 2 - d * (u : ℤ) ^ 2 = 4 := CNPell.main d hd hpos
