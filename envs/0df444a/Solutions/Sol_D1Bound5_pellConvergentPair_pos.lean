-- Prove2me | solution 1 for D1Bound5.pellConvergentPair_pos
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:17.78471+00:00
-- url     : https://prove2.me/submissions/c6878add-e901-40a7-9b65-e3a017658739

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
    0 < (pellConvergentPair x n).1 ∧ 0 < (pellConvergentPair x n).2 := by
  induction n generalizing x with
  | zero =>
      have hf : (1 : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by simpa using hx1.le)
      simpa only [pellConvergentPair] using And.intro (by omega : 0 < ⌊x⌋)
        (by norm_num : (0 : ℤ) < 1)
  | succ n ih =>
      obtain ⟨hp,hq⟩ := ih (pell_tail_irrational hx) (pell_tail_gt_one hx)
      have hf : (1 : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by simpa using hx1.le)
      change 0 < ⌊x⌋ * (pellConvergentPair (Int.fract x)⁻¹ n).1 +
        (pellConvergentPair (Int.fract x)⁻¹ n).2 ∧
        0 < (pellConvergentPair (Int.fract x)⁻¹ n).1
      exact ⟨by positivity, hp⟩















end D1Bound5
end
