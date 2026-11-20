-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_first_negative_mark_prearrival_finite_barrier_reserve_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:42:06.281126+00:00
-- url     : https://prove2.me/submissions/2394ce01-ee6d-4172-983b-67bf1ae9fd9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_before_strict_upcrossing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B J : ℝ≥0 → ℝ) (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t + J t)
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hJzero : ∀ t : ℝ≥0, t < σ → J t = 0) :
    ∀ t : ℝ≥0, t < σ →
      0 < riskProcess X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) t ω := by
  have hExit : (σ : ℝ≥0∞) ≤
      (⨅ (s : ℝ≥0)
        (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
        (s : ℝ≥0∞)) := by
    refine le_iInf fun s => le_iInf fun hs => ?_
    by_contra hn
    have hlt : s < σ := lt_of_not_ge (by exact_mod_cast hn)
    have hsmall := abs_lt.mp (hTube s (le_of_lt hlt))
    rw [hPath s, hJzero s hlt] at hs
    norm_num at hs
    linarith
  intro t ht
  have hpre :
      (t : ℝ≥0∞) <
        (⨅ (s : ℝ≥0)
          (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
          (s : ℝ≥0∞)) := by
    have htc : (t : ℝ≥0∞) < (σ : ℝ≥0∞) := by
      exact_mod_cast ht
    exact htc.trans_le hExit
  have heq := (riskProcess_before_strict_upcrossing
      X (1 / 10 : ℝ) (1 / 5 : ℝ) t ω hpre).1
  rw [heq, hPath t, hJzero t ht]
  have hB := abs_lt.mp (hTube t (le_of_lt ht))
  linarith
