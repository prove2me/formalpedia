-- Prove2me | solution 1 for D1Bound5.pellConvergentPair_step_mono
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:13.666886+00:00
-- url     : https://prove2.me/submissions/d3f54f25-456b-4768-9b1c-c60508605aaf

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellConvergentCompleteness_Definitions

section
namespace D1Bound5



private theorem pell_tail_irrational {x : ℝ} (hx : Irrational x) :
    Irrational (Int.fract x)⁻¹ := by
  exact (show Irrational (x - (⌊x⌋ : ℝ)) from hx.sub_intCast _).inv

private theorem pell_tail_gt_one {x : ℝ} (hx : Irrational x) :
    1 < (Int.fract x)⁻¹ := by
  have hfr : 0 < Int.fract x := Int.fract_pos.mpr (hx.ne_int _)
  exact (one_lt_inv₀ hfr).mpr (Int.fract_lt_one x)







theorem _root_.solution {x : ℝ} (hx : Irrational x) (hx1 : 1 < x)
    (n : ℕ) :
    (pellConvergentPair x n).1 ≤ (pellConvergentPair x (n+1)).1 ∧
    (pellConvergentPair x n).2 ≤ (pellConvergentPair x (n+1)).2 := by
  induction n generalizing x with
  | zero =>
      have hf : (1 : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by simpa using hx1.le)
      have ht : (1 : ℤ) ≤ ⌊(Int.fract x)⁻¹⌋ :=
        Int.le_floor.mpr (by simpa using (pell_tail_gt_one hx).le)
      simp only [pellConvergentPair]
      constructor
      · nlinarith
      · exact ht
  | succ n ih =>
      have hf : (1 : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by simpa using hx1.le)
      obtain ⟨hp,hq⟩ := ih (pell_tail_irrational hx) (pell_tail_gt_one hx)
      simp only [pellConvergentPair]
      constructor
      · exact add_le_add (mul_le_mul_of_nonneg_left hp (by omega)) hq
      · exact hp









end D1Bound5
end
