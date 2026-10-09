-- Prove2me | solution 1 for BookProof.ChapterF4.countsketch_unbiased
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:01:31.723237+00:00
-- url     : https://prove2.me/submissions/cd1bac30-c1db-4545-a5e1-5cf9f6ab6d67

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.countsketch_unbiased
import Mathlib
import Definitions.Def_ChapterF4
import Theorems.Thm_BookProof_ChapterF4_sign_pair_expectation
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (h : Fin d → Fin k) (x y : Fin d → ℝ) :
    expectation (fun ω => ∑ j, csketch h ω x j * csketch h ω y j) = ∑ c, x c * y c := by

  -- Apply the linearity of the expectation and the fact that `sgn (ω c)` are independent Rademacher
  -- variables.
  have h_exp : ∑ ω : Fin d → Bool,    (∑ j : Fin k, csketch h ω x j * csketch h ω y j) = ∑ c,    ∑
      c', (if h c = h c' then (∑ ω : Fin d → Bool, sgn (ω c) * sgn (ω c')) * (x c * y c') else 0) :=
          by
    have h_exp : ∀ ω : Fin d → Bool,      ∑ j : Fin k,      csketch h ω x j * csketch h ω y j = ∑ c,
        ∑ c', (if h c = h c' then sgn (ω c) * sgn (ω c') * (x c * y c') else 0) := by
      intro ω;
      simp only [csketch, Finset.sum_ite, Finset.sum_const_zero, add_zero];
      simp only [mul_comm, Finset.sum_mul _ _ _, Finset.mul_sum, mul_left_comm, mul_assoc];
      simp only [Finset.sum_sigma'];
      refine Finset.sum_bij ( fun x hx => ⟨ x.snd.fst, x.snd.snd ⟩ ) ?_ ?_ ?_ ?_ <;> aesop;
    simp only [h_exp, Finset.sum_mul];
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ =>
        by split_ifs <;> simp [ * ] );
  convert congr_arg ( fun x : ℝ => x / 2 ^ d ) h_exp using 1
  · rw [ expectation, Finset.sum_div ]
  · rw [ Finset.sum_div _ _ _ ] ;    congr ;    ext c ;    rw [ Finset.sum_eq_single c ] <;> simp
      +contextual [ sign_pair_expectation ] <;> (first
        | exact fun b hne _ habc => (hne habc.symm).elim
        | ring
        | grind)
