-- Prove2me | solution 1 for D1Bound5.QuadInt.rootCandidate_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:28.714984+00:00
-- url     : https://prove2.me/submissions/e56cf629-a22c-4736-9fb4-45bc5845c769

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_exists_normalized_root
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
namespace D1Bound5.QuadInt

variable {tau nu : ℤ}

/-- Algebraic identities underlying the full-ring square test. -/
theorem square_coordinates (r : QuadInt tau nu) :
    (r*r).norm = r.norm^2 ∧
    (2*r.re+tau*r.im)^2 = 2*r.norm+(2*(r*r).re+tau*(r*r).im) ∧
    discriminant tau nu*r.im^2 = 2*r.norm-(2*(r*r).re+tau*(r*r).im) ∧
    (2*r.re+tau*r.im)*r.im = (r*r).im := by
  refine ⟨by rw [map_mul, pow_two], ?_, ?_, ?_⟩
  all_goals simp only [norm_formula, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, discriminant]
  all_goals ring









/-- Completeness of the exact candidate, for every positive-discriminant
coordinate ring and arbitrary input size. No nonzero-root assumption occurs. -/
theorem _root_.solution (hd : 0 < discriminant tau nu)
    {z : QuadInt tau nu} (hz : ∃ r, r*r = z) : rootCandidate z*rootCandidate z = z := by
  obtain ⟨r, hr, hE, haxis⟩ := exists_normalized_root hz
  obtain ⟨hN, he, hf, hI⟩ := square_coordinates r
  rw [hr] at hN he hf hI
  have hn : Int.sqrt z.norm = r.norm := by
    rw [hN, pow_two, Int.sqrt_eq, Int.natCast_natAbs, abs_of_nonneg (norm_nonneg hd r)]
  have he' : Int.sqrt (2*r.norm+(2*z.re+tau*z.im)) = 2*r.re+tau*r.im := by
    rw [← he, pow_two, Int.sqrt_eq, Int.natCast_natAbs, abs_of_nonneg hE]
  have hf' : Int.sqrt ((2*r.norm-(2*z.re+tau*z.im))/discriminant tau nu) = |r.im| := by
    rw [← hf]
    simp only [Int.mul_ediv_cancel_left _ (ne_of_gt hd), pow_two, Int.sqrt_eq, Int.natCast_natAbs]
  have hisign : (if z.im < 0 then -|r.im| else |r.im|) = r.im := by
    by_cases hneg : z.im < 0
    · have hrneg : r.im < 0 := by
        by_contra h
        have hmul := mul_nonneg hE (le_of_not_gt h)
        rw [hI] at hmul
        omega
      simp [hneg, abs_of_neg hrneg]
    · have hrnonneg : 0 ≤ r.im := by
        by_cases he0 : 2*r.re+tau*r.im = 0
        · exact haxis he0
        · have hep : 0 < 2*r.re+tau*r.im := by omega
          by_contra h
          have hmul := mul_neg_of_pos_of_neg hep (lt_of_not_ge h)
          rw [hI] at hmul
          exact hneg hmul
      simp [hneg, abs_of_nonneg hrnonneg]
  have hc : rootCandidate z = r := by
    unfold rootCandidate
    dsimp only
    rw [hn, he', hf', hisign]
    apply QuadraticAlgebra.ext
    · change (2*r.re+tau*r.im-tau*r.im)/2 = r.re
      omega
    · rfl
  rw [hc]
  exact hr













end D1Bound5.QuadInt
end
