-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_character_sum_range_le
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:38:18.583903+00:00
-- url     : https://prove2.me/submissions/552c58ea-dabd-4015-8b9c-532acf768985

import Mathlib
open Finset


theorem solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ q := by
  have hperiod (m : ℕ) : (∑ n ∈ range (q+m), χ (n : ZMod q)) = ∑ n ∈ range m, χ (n : ZMod q) := by
    have hz : (∑ n ∈ range q, χ (n : ZMod q)) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      convert (MulChar.sum_eq_zero_of_ne_one hχ) using 1
      exact (Fintype.sum_equiv (ZMod.finEquiv q).toEquiv _ _ (by
        intro i; congr 1; cases q with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ q => apply Fin.ext; exact Nat.mod_eq_of_lt i.isLt)).symm.symm
    rw [Finset.sum_range_add, hz, zero_add]; simp
  have bound (m : ℕ) : ‖∑ n ∈ range m, χ (n : ZMod q)‖ ≤ (q:ℝ) := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases h : m < q
      · calc
          _ ≤ ∑ n ∈ range m, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
          _ ≤ ∑ _ ∈ range m, (1:ℝ) := Finset.sum_le_sum fun n _ => χ.norm_le_one _
          _ ≤ _ := by simpa using (show (m:ℝ) ≤ q by exact_mod_cast h.le)
      · have he : m = q + (m-q) := by omega
        rw [show (∑ n ∈ range m, χ (n : ZMod q)) = ∑ n ∈ range (m-q), χ (n : ZMod q) by conv_lhs => rw [he]; exact hperiod _]
        apply ih; have := NeZero.pos q; omega
  exact bound M
