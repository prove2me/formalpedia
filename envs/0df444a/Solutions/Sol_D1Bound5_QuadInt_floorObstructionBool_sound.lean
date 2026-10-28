-- Prove2me | solution 1 for D1Bound5.QuadInt.floorObstructionBool_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:16.060995+00:00
-- url     : https://prove2.me/submissions/d82c9e09-1e99-4ba5-9c9e-bc9d72b659e1

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_QuadSquareFloorObstruction_Definitions
import Theorems.Thm_D1Bound5_integer_square_floor_obstruction
import Theorems.Thm_D1Bound5_negative_integer_square_floor_obstruction_trace_one
import Theorems.Thm_D1Bound5_negative_integer_square_floor_obstruction_trace_zero
import Theorems.Thm_D1Bound5_positive_integer_square_is_integer

section
namespace D1Bound5





/-- Positive rational radicands in an imaginary quadratic coordinate
ring reduce to ordinary integer squares. -/
theorem positive_integer_square_floor_obstruction {tau nu m k : ℤ}
    (hd : 0 < QuadInt.discriminant tau nu) (hk : 0 ≤ k)
    (hlo : k ^ 2 < m) (hhi : m < (k + 1) ^ 2) :
    ¬ ∃ r : QuadInt tau nu, r * r = (m : QuadInt tau nu) := by
  intro hr
  have hm : 0 < m := lt_of_le_of_lt (sq_nonneg k) hlo
  exact integer_square_floor_obstruction hk hlo hhi
    (positive_integer_square_is_integer hd hm hr)





namespace QuadInt

/-- A nonsquare algebraic norm rules out a square radicand, without
any discriminant, nonzero, or coordinate-sign hypothesis. -/
theorem norm_nonsquare_obstruction {tau nu : ℤ} (z : QuadInt tau nu)
    (h : ¬ ∃ n : ℤ, z.norm = n ^ 2) :
    ¬ ∃ r : QuadInt tau nu, r * r = z := by
  rintro ⟨r, hr⟩
  apply h
  refine ⟨r.norm, ?_⟩
  rw [← hr, map_mul, pow_two]

/-- A floor witness for the algebraic norm is a square obstruction for
an arbitrary radicand. In particular, the radicand need not be real. -/
theorem norm_floor_obstruction {tau nu k : ℤ} (z : QuadInt tau nu)
    (hk : 0 ≤ k) (hlo : k ^ 2 < z.norm) (hhi : z.norm < (k + 1) ^ 2) :
    ¬ ∃ r : QuadInt tau nu, r * r = z :=
  norm_nonsquare_obstruction z (integer_square_floor_obstruction hk hlo hhi)



/-- Soundness of the inexpensive floor-witness checker. It uses the
accepted rational-square classification and multiplicativity of norm;
no candidate square root is computed. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) {z : QuadInt tau nu} {k : ℕ}
    (h : floorObstructionBool z k = true) :
    ¬ ∃ r : QuadInt tau nu, r * r = z := by
  have hk : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  by_cases him : z.im = 0
  · have hz : z = (z.re : QuadInt tau nu) := by
      apply QuadraticAlgebra.ext
      · simp only [QuadraticAlgebra.re_intCast, Int.cast_id]
      · simpa only [QuadraticAlgebra.im_intCast] using him
    by_cases hm : 0 < z.re
    · have hf : (k : ℤ) ^ 2 < z.re ∧ z.re < ((k : ℤ) + 1) ^ 2 := by
        simpa only [floorObstructionBool, if_pos him, if_pos hm, decide_eq_true_eq] using h
      intro hr
      apply positive_integer_square_floor_obstruction hd hk hf.1 hf.2
      simpa only [← hz] using hr
    · by_cases ht0 : tau = 0
      · subst tau
        have hnu : 0 < nu := by
          dsimp [discriminant] at hd
          norm_num at hd
          omega
        have hf : nu * (k : ℤ) ^ 2 < -z.re ∧
            -z.re < nu * ((k : ℤ) + 1) ^ 2 := by
          simpa only [floorObstructionBool, if_pos him, if_neg hm,
            if_pos (rfl : (0 : ℤ) = 0), if_true, decide_eq_true_eq] using h
        intro hr
        apply negative_integer_square_floor_obstruction_trace_zero hnu hk hf.1 hf.2
        simpa only [← hz] using hr
      · by_cases ht1 : tau = 1
        · subst tau
          have hd' : 0 < 4 * nu - 1 := by simpa only [discriminant, one_pow] using hd
          have hf : (4 * nu - 1) * (k : ℤ) ^ 2 < -z.re ∧
              -z.re < (4 * nu - 1) * ((k : ℤ) + 1) ^ 2 := by
            simpa only [floorObstructionBool, if_pos him, if_neg hm,
              if_neg ht0, if_pos (rfl : (1 : ℤ) = 1), if_true, decide_eq_true_eq] using h
          intro hr
          apply negative_integer_square_floor_obstruction_trace_one hd' hk hf.1 hf.2
          simpa only [← hz] using hr
        · simp only [floorObstructionBool, if_pos him, if_neg hm,
            if_neg ht0, if_neg ht1, Bool.false_eq_true] at h
  · have hf : (k : ℤ) ^ 2 < z.norm ∧ z.norm < ((k : ℤ) + 1) ^ 2 := by
      simpa only [floorObstructionBool, if_neg him, decide_eq_true_eq] using h
    exact norm_floor_obstruction z hk hf.1 hf.2

end QuadInt
end D1Bound5
end
