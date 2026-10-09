-- Prove2me | solution 1 for BookProof.ChapterF4.sign_pair_expectation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:01:30.57021+00:00
-- url     : https://prove2.me/submissions/b79eed62-99a3-4d98-a040-702e6c20193b

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.sign_pair_expectation
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c c' : Fin d) :
    (∑ ω : Fin d → Bool, sgn (ω c) * sgn (ω c')) = if c = c' then (2 ^ d : ℝ) else 0 := by

  by_cases h : c = c';
  · simp [ ← sq, h, sgn_sq ];
  · -- For $c \ne c'$, we can pair each $\omega$ with $\omega'$ where $\omega'$ differs from
    -- $\omega$ only at position $c$.
    have h_pair : ∑ ω : Fin d → Bool,      sgn (ω c) * sgn (ω c') = ∑ ω : Fin d → Bool, -sgn (ω c) *
        sgn (ω c') := by
      apply Finset.sum_bij (fun ω _ => Function.update ω c (¬ω c));
      · simp;
      · intro a₁ _ a₂ _ h; ext i; by_cases hi : i = c <;> replace h := congr_fun h i <;> aesop;
      · exact fun b _ => ⟨ Function.update b c ( ¬b c ), Finset.mem_univ _, by aesop ⟩;
      · simp [ sgn ];
        grind;
    norm_num [ Finset.sum_neg_distrib, neg_mul ] at * ; split_ifs ; linarith
