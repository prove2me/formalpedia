-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite15_original_sampled_preexit_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T16:45:05.7442+00:00
-- url     : https://prove2.me/submissions/2ce3250d-7479-4e0d-93ad-a3af9d589572

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Each original sampled postpayment reserve before the first bad sample
satisfies the same deterministic pre-exit lower floor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (r : ℕ → ℝ≥0) (δ : ℝ) :
    ∀ (ω : Ω) (n : ℕ),
      (r n : WithTop ℝ≥0) <
        (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < δ
          then (r k : WithTop ℝ≥0) else ⊤) →
      δ ≤ x + X.X (r n) ω - rightLimit D (r n) ω := by
  intro ω n hn
  by_contra h
  have hlt : x + X.X (r n) ω - rightLimit D (r n) ω < δ :=
    lt_of_not_ge h
  have hle :
      (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ
        then (r k : WithTop ℝ≥0) else ⊤) ≤
        (r n : WithTop ℝ≥0) := by
    calc
      (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ
        then (r k : WithTop ℝ≥0) else ⊤) ≤
          (if x + X.X (r n) ω - rightLimit D (r n) ω < δ
           then (r n : WithTop ℝ≥0) else ⊤) := iInf_le _ n
      _ = (r n : WithTop ℝ≥0) := if_pos hlt
  exact (not_lt_of_ge hle) hn
