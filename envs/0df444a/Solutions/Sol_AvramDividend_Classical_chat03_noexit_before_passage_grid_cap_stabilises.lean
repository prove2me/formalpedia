-- Prove2me | solution 1 for AvramDividend.Classical.chat03_noexit_before_passage_grid_cap_stabilises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T15:06:59.482457+00:00
-- url     : https://prove2.me/submissions/7bbcdfb2-daf3-48e6-b13b-78e6046600aa

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_sampled_clock_caps_to_horizon
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal
open AvramDividend.Classical

/-!
A continuous strict exit infimum strictly after the fixed horizon
forces the actual bounded grid clock to stop exactly at the horizon
when sufficiently fine terminal times lie between those two times.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hT : T < τ)
    (mesh : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hterm : ∀ᶠ n in atTop,
      T ≤ (m n : ℝ≥0) * mesh n ∧
      (m n : ℝ≥0) * mesh n < τ)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    ∀ᶠ n in atTop, min ((K n ω : ℝ≥0) * mesh n) T = T := by
  filter_upwards [hterm] with n hn
  rw [hK n ω]
  apply chat03_noexit_sampled_clock_caps_to_horizon
    X ω lower upper (mesh n) T (m n) hn.1
  intro t ht he
  exact (not_lt_of_ge (hτ.1 he)) (lt_of_le_of_lt ht hn.2)
