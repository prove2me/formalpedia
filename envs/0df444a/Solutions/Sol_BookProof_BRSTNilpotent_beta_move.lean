-- Prove2me | solution 1 for BookProof.BRSTNilpotent.beta_move
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T14:14:47.237899+00:00
-- url     : https://prove2.me/submissions/904e4794-1a58-46bd-9e33-33d7dfc6f4ae

-- Generated from ChapterBRSTNilpotent.lean — solution of BookProof.BRSTNilpotent.beta_move
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent













variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (χ β : Fin n → R) (hCAR : GhostCAR χ β) (e d g : Fin n) :
    β e * (χ d * χ g)
      = (if e = d then χ g else 0) - (if e = g then χ d else 0) + χ d * χ g * β e := by

  have h_combined : β e * (χ d * χ g) = (β e * χ d) * χ g := by
    rw [ mul_assoc ];
  convert congr_arg ( · * χ g ) ( show β e * χ d = ( if e = d then 1 else 0 ) - χ d * β e from ?_ )
                        using 1;
  · have := hCAR.betachi e g; simp_all only [mul_assoc, sub_mul, ite_mul, one_mul, zero_mul] ;
    split_ifs <;>
      simp_all only [← eq_sub_iff_add_eq', sub_self, zero_add, ↓reduceIte, sub_zero, zero_sub,
        mul_neg, sub_sub_cancel_left, sub_neg_eq_add];
    · rw [ mul_sub, mul_one ];
    · grind;
  · exact eq_sub_of_add_eq ( hCAR.betachi e d )
