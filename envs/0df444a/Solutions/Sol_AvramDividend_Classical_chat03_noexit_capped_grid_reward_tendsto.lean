-- Prove2me | solution 1 for AvramDividend.Classical.chat03_noexit_capped_grid_reward_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T15:16:58.412493+00:00
-- url     : https://prove2.me/submissions/893a8f56-df25-4d76-bf58-3fd66ddf97fb

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_before_passage_grid_cap_stabilises
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Any capped grid reward, including the stopped discounted scale value,
converges exactly on paths whose strict exit follows the horizon.
This requires no reward continuity because the capped clock stabilises.
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
      (Set.Ioi (0 : ℝ)) 0 (m n) η)
    (reward : ℝ≥0 → ℝ) :
    Tendsto (fun n =>
      reward (min ((K n ω : ℝ≥0) * mesh n) T))
      atTop (𝓝 (reward T)) := by
  have hevent :
      (fun _ : ℕ => reward T) =ᶠ[atTop]
      (fun n => reward (min ((K n ω : ℝ≥0) * mesh n) T)) := by
    filter_upwards [
      chat03_noexit_before_passage_grid_cap_stabilises
        X ω lower upper τ T hτ hT mesh m hterm K hK] with n hn
    rw [hn]
  exact tendsto_const_nhds.congr' hevent
