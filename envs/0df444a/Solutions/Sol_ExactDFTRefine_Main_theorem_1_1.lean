-- Prove2me | solution 1 for ExactDFTRefine.Main.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:48:39.281109+00:00
-- url     : https://prove2.me/submissions/38740dd8-84d4-4326-853f-eda26e50b5cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_RAM
import Definitions.Def_ExactDFTRefine_Main_Moments
import Theorems.Thm_ExactDFTRefine_Main_beta_bound
import Theorems.Thm_ExactDFTRefine_Main_loglog_absorption

open Asymptotics Filter

namespace ExactDFTRefine.Main

/-- **Theorem 1.1**, p. 2. In the exact complex-arithmetic RAM model of Section 2 there are fixed
deterministic programs (a root-order program and a transform program) and a constant `c` such
that for every `n ≥ 1` and every `x ∈ ℂ^n` the run computes `DFT_n x` with `1 ≤ D(n) < 1024 n^3`,
one supplied root, all integer values and addresses at most `(n + 2)^c`, and total work
`W(n) = O(n (log n)^{1-δ})`, `δ = 30201659/10^10`. -/
theorem _root_.solution :
    ∃ (P₁ P₂ : Program) (c : ℕ) (K : ℝ) (n₀ : ℕ), 0 < K ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x : Fin n → ℂ, ∃ W : ℕ, DFTRun P₁ P₂ c n x W ∧
        (n₀ ≤ n → (W : ℝ) ≤ K * n * Real.log (n : ℝ) ^ (1 - delta)) := by
  obtain ⟨P₁, P₂, c, K, n₀, hK, hrun⟩ := beta_bound.2.2
  have hlittle := loglog_absorption.2
  have hev : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (Real.log (n : ℝ)) ^ 2‖ ≤
        (1 : ℝ) * ‖Real.log (n : ℝ) ^ (beta - delta)‖ :=
    hlittle.def (c := (1 : ℝ)) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨P₁, P₂, c, K, max n₀ (max N 2), hK, ?_⟩
  intro n hn x
  obtain ⟨W, hWrun, hWbound⟩ := hrun n hn x
  refine ⟨W, hWrun, ?_⟩
  intro hnlarge
  have hn₀le : n₀ ≤ n := (le_max_left n₀ (max N 2)).trans hnlarge
  have hNle : N ≤ n :=
    ((le_max_left N 2).trans (le_max_right n₀ (max N 2))).trans hnlarge
  have hn2 : 2 ≤ n :=
    ((le_max_right N 2).trans (le_max_right n₀ (max N 2))).trans hnlarge
  have hnreal : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hfactor :
      Real.log (Real.log (n : ℝ)) ^ 2 ≤
        Real.log (n : ℝ) ^ (beta - delta) := by
    have hloglog : 0 ≤ Real.log (Real.log (n : ℝ)) ^ 2 := by positivity
    have hrpow : 0 ≤ Real.log (n : ℝ) ^ (beta - delta) :=
      Real.rpow_nonneg hlog.le _
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg hloglog,
      abs_of_nonneg hrpow] using hN n hNle
  have hmulnonneg :
      0 ≤ K * (n : ℝ) * Real.log (n : ℝ) ^ (1 - beta) :=
    mul_nonneg (mul_nonneg hK.le (Nat.cast_nonneg n))
      (Real.rpow_nonneg hlog.le _)
  have hmul := mul_le_mul_of_nonneg_left hfactor hmulnonneg
  have hpow :
      Real.log (n : ℝ) ^ (1 - beta) *
          Real.log (n : ℝ) ^ (beta - delta) =
        Real.log (n : ℝ) ^ (1 - delta) := by
    rw [← Real.rpow_add hlog]
    have hexp : (1 - beta) + (beta - delta) = 1 - delta := by ring
    rw [hexp]
  calc
    (W : ℝ) ≤ K * (n : ℝ) * Real.log (n : ℝ) ^ (1 - beta) *
        Real.log (Real.log (n : ℝ)) ^ 2 := hWbound hn₀le
    _ ≤ (K * (n : ℝ) * Real.log (n : ℝ) ^ (1 - beta)) *
        Real.log (n : ℝ) ^ (beta - delta) := hmul
    _ = K * (n : ℝ) *
        (Real.log (n : ℝ) ^ (1 - beta) *
          Real.log (n : ℝ) ^ (beta - delta)) := by ring
    _ = K * (n : ℝ) * Real.log (n : ℝ) ^ (1 - delta) := by rw [hpow]

end ExactDFTRefine.Main
