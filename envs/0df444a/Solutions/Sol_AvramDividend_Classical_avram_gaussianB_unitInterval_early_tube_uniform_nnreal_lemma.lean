-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:51:21.900851+00:00
-- url     : https://prove2.me/submissions/877e1fd7-4f2e-4291-86d2-20b98e564abf

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.NormNum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section
/-- UnitInterval tube control covers all true short NNReal source times. -/
theorem solution
    (f : ℝ≥0 → ℝ) (R : ℝ)
    (hTube : ∀ u : unitInterval,
      u ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
      f ⟨u, u.2.1⟩ ≤ R) :
    ∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) → f t ≤ R := by
  intro t ht
  have htR : (t : ℝ) ≤ (1 / 1000 : ℝ) := by
    exact_mod_cast ht
  have ht1 : (t : ℝ) ≤ 1 :=
    htR.trans (by norm_num)
  let u : unitInterval := ⟨(t : ℝ), ⟨t.property, ht1⟩⟩
  have hu : u ≤
      (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) := by
    change (t : ℝ) ≤ (17 / 16000 : ℝ)
    exact htR.trans (by norm_num)
  have hPt : (⟨u, u.2.1⟩ : ℝ≥0) = t := by
    apply Subtype.ext
    rfl
  simpa only [hPt] using hTube u hu
