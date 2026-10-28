-- Prove2me | solution 1 for D1Bound5.pellConvergentPair_div
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:35:15.189004+00:00
-- url     : https://prove2.me/submissions/d22729eb-c205-45d9-ac9f-97d691bf2024

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellConvergentCompleteness_Definitions
import Theorems.Thm_D1Bound5_pellConvergentPair_pos

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
    ((pellConvergentPair x n).1 : ℚ) / (pellConvergentPair x n).2 = x.convergent n := by
  induction n generalizing x with
  | zero => simp [pellConvergentPair]
  | succ n ih =>
      have ht := pell_tail_irrational hx
      have ht1 := pell_tail_gt_one hx
      obtain ⟨hp,hq⟩ := pellConvergentPair_pos ht ht1 n
      have hp' : ((pellConvergentPair (Int.fract x)⁻¹ n).1 : ℚ) ≠ 0 := by
        exact_mod_cast hp.ne'
      have hq' : ((pellConvergentPair (Int.fract x)⁻¹ n).2 : ℚ) ≠ 0 := by
        exact_mod_cast hq.ne'
      rw [Real.convergent_succ, ← ih ht ht1]
      simp only [pellConvergentPair, Int.cast_add, Int.cast_mul]
      field_simp [hp', hq']
      <;> ring











end D1Bound5
end
