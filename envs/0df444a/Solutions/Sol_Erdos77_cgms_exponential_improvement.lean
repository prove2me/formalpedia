-- Prove2me | solution 1 for Erdos77.cgms_exponential_improvement
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:01:23.531978+00:00
-- url     : https://prove2.me/submissions/622a299d-8a76-4aee-8fbb-f62d0b03167b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_cgms_log_growth_gap

theorem solution :
  Exists (fun epsilon : Real =>
    And (0 < epsilon) (Filter.Eventually (fun k : Nat =>
      (Erdos77.diagonalRamsey k : Real) <= (4 - epsilon) ^ k) Filter.atTop)) := by
  apply Exists.elim Erdos77_cgms_log_growth_gap
  intro a h
  have ha : 0 < a := h.1
  have ha4 : a < 4 := h.2.1
  have hbound := h.2.2
  refine Exists.intro (4 - a) ?_
  constructor
  · linarith
  · filter_upwards [hbound] with k hk
    have h₁ : (Erdos77.diagonalRamsey k : Real) <= Real.exp ((k : Real) * Real.log a) :=
      Real.le_exp_of_log_le hk
    have h₂ : Real.exp ((k : Real) * Real.log a) = a ^ k := by
      calc
        Real.exp ((k : Real) * Real.log a) = Real.exp (Real.log a * (k : Real)) := by
          congr 1 <;> ring
        _ = a ^ (k : Real) := (Real.rpow_def_of_pos ha _).symm
        _ = a ^ k := Real.rpow_natCast a k
    have h₃ : 4 - (4 - a) = a := by ring
    rw [h₃]
    exact h₁.trans_eq h₂
