-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_cap_state_marked_jump_kernel_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:43:56.560244+00:00
-- url     : https://prove2.me/submissions/5da60635-db01-4118-a137-281893609e6c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_strict_cofinal_rows_never_contain_upper_cap_reserve
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- At a capped reserve the exact original marked negative-jump kernel is zero,
since all physical spatial bands omit the upper cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n : ℕ) (t : ℝ≥0) (ω : Ω) (z : ℝ)
    (hcap : ENNReal.ofReal
        (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) = C) :
    (if
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∈
            Icc (a n) (b n) ∧ z < 0
      then
        Real.exp (-(q * (t : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
      else 0) = 0 := by
  have hnot :
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∉
          Icc (a n) (b n) :=
    avram_bva_a22_original_strict_cofinal_rows_never_contain_upper_cap_reserve
      C a b ha hinside n _ hcap
  simp [hnot]
