-- Prove2me | solution 1 for Freiman.form_minimum_infimum_assembly
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:15:44.738155+00:00
-- url     : https://prove2.me/submissions/ace381b3-7065-49ed-874f-cf796ba064b0

import Definitions.Def_Freiman_reducedForms

open Freiman

set_option autoImplicit false

private theorem value_set_nonempty (A B C : ℝ) :
    {v : ℝ | ∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧ v = |quadraticValue A B C p q|}.Nonempty :=
  ⟨|quadraticValue A B C 1 0|, 1, 0, Or.inl (by norm_num), rfl⟩

private theorem value_set_bdd (A B C : ℝ) :
    BddBelow {v : ℝ | ∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧ v = |quadraticValue A B C p q|} := by
  refine ⟨0, ?_⟩
  rintro v ⟨p, q, hpq, rfl⟩
  exact abs_nonneg _

theorem solution (R : ReducedOrbit)
    (hinv : ∀ n : ℤ, reducedMinimum (R.alpha n) (R.beta n) =
      reducedMinimum (R.alpha 0) (R.beta 0))
    (hlower : ∀ n p q : ℤ, (p ≠ 0 ∨ q ≠ 0) →
      orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q|) :
    reducedMinimum (R.alpha 0) (R.beta 0) = orbitReciprocalInfimum R := by
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty _)
    rintro v ⟨n, rfl⟩
    change reducedMinimum (R.alpha 0) (R.beta 0) ≤ 1 / (R.alpha n + R.beta n)
    rw [← hinv n]
    have ha := R.alpha_gt n
    have hb := R.beta_pos n
    have hden : 0 < R.alpha n + R.beta n := by linarith
    have hpoint : |quadraticValue (reducedA (R.alpha n) (R.beta n))
        (reducedB (R.alpha n) (R.beta n)) (reducedC (R.alpha n) (R.beta n)) 1 0| =
        1 / (R.alpha n + R.beta n) := by
      simp only [quadraticValue, Int.cast_one, Int.cast_zero, one_pow,
        zero_pow (by norm_num : 2 ≠ 0), mul_one, mul_zero, add_zero, reducedA]
      exact abs_of_pos (one_div_pos.mpr hden)
    unfold reducedMinimum quadraticMinimum
    rw [← hpoint]
    exact csInf_le (value_set_bdd _ _ _) ⟨1, 0, Or.inl (by norm_num), rfl⟩
  · unfold reducedMinimum quadraticMinimum
    apply le_csInf (value_set_nonempty _ _ _)
    rintro v ⟨p, q, hpq, rfl⟩
    exact hlower 0 p q hpq
