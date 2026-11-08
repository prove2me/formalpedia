-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:07:49.117394+00:00
-- url     : https://prove2.me/submissions/9d228dd9-c73b-4a1d-87dc-64c79cd815e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Source-exact infinite-cap admissibility conditional on the strict right-limit identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hstrategy : IsDividendStrategy 𝓕 (fun t ω => if t = 0 then 0 else K ω))
    (hright : ∀ ω (t : ℝ≥0),
      rightLimit (fun s ω => if s = 0 then 0 else K ω) t ω = K ω)
    (hKle : ∀ ω, K ω ≤ x) :
    IsAdmissibleLe X x ⊤ (fun t ω => if t = 0 then 0 else K ω) := by
  let D : ℝ≥0 → Ω → ℝ := fun t ω => if t = 0 then 0 else K ω
  change IsAdmissible X x D ∧
    ∀ ω (t : ℝ≥0), 0 < t → ENNReal.ofReal (riskProcess X x D t ω) ≤ ⊤
  refine ⟨⟨hstrategy, ?_⟩, ?_⟩
  · intro ω t ht
    rcases ht with hzero | hpre
    · subst t
      simpa [D, riskProcess, X.X_zero ω, hright ω 0] using hKle ω
    · by_cases hzero : t = 0
      · subst t
        simpa [D, riskProcess, X.X_zero ω, hright ω 0] using hKle ω
      · have hrisk : 0 ≤ riskProcess X x D t ω :=
          riskProcess_nonneg_before_ruin X x D ω t hpre
        have hdiff : rightLimit D t ω - D t ω = 0 := by
          rw [hright ω t]
          simp [D, hzero]
        simpa only [hdiff] using hrisk
  · intro ω t ht
    exact le_top
