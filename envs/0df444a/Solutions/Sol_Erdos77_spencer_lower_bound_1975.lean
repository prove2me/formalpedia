-- Prove2me | solution 1 for Erdos77.spencer_lower_bound_1975
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:29:24.547981+00:00
-- url     : https://prove2.me/submissions/cc3f2664-fd46-4d72-b7e0-00dd57a824a0

import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_spencer_1975_lll_bad_graph_criterion
import Theorems.Thm_Erdos77_spencer_1975_lll_asymptotic_threshold
import Theorems.Thm_Erdos77_spencer_1975_finite_and_bad_graph_bound
import Theorems.Thm_Erdos77_erdos_1947_ramsey_finiteness

open Filter

theorem solution (ε : Real) (hε : 0 < ε) :
    ∀ᶠ k : Nat in atTop,
      (1 - ε) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
          (2 : Real) ^ ((k : Real) / 2) ≤
        (Erdos77.diagonalRamsey k : Real) := by
  by_cases hεge : 1 ≤ ε
  · filter_upwards with k
    have hfactor : 1 - ε ≤ 0 := by linarith
    have hscale : 0 ≤ (Real.sqrt 2 / Real.exp 1) * (k : Real) *
        (2 : Real) ^ ((k : Real) / 2) := by positivity
    have hlhs : (1 - ε) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
        (2 : Real) ^ ((k : Real) / 2) ≤ 0 := by
      have hmul : (1 - ε) * ((Real.sqrt 2 / Real.exp 1) * (k : Real) *
          (2 : Real) ^ ((k : Real) / 2)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hfactor hscale
      nlinarith
    exact hlhs.trans (Nat.cast_nonneg _)
  · have hεlt : ε < 1 := lt_of_not_ge hεge
    have hthreshold := Erdos77.spencer_1975_lll_asymptotic_threshold ε hε hεlt
    filter_upwards [hthreshold] with k hk
    rcases hk with ⟨hk2, hkn, hcond⟩
    let n := Nat.floor
      ((1 - ε) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
        (2 : Real) ^ ((k : Real) / 2))
    have hbad := Erdos77.spencer_1975_lll_bad_graph_criterion k n hk2 hkn hcond
    have hk1 : 1 ≤ k := le_trans (by decide) hk2
    have hfinite := Erdos77.erdos_1947_ramsey_finiteness k hk1
    have hR := Erdos77.spencer_1975_finite_and_bad_graph_bound k n hfinite hbad
    have hfloor :
        (1 - ε) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
          (2 : Real) ^ ((k : Real) / 2) ≤ (n : Real) + 1 := by
      dsimp [n]
      exact (Nat.lt_floor_add_one _).le
    exact hfloor.trans hR
