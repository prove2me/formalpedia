-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_only_affine_hjump_all_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:17:25.434696+00:00
-- url     : https://prove2.me/submissions/0c6d658f-89ce-4c57-8b72-f04b1dfff146

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_rightlimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The initial dividend jump loses exactly its size for an affine value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKle : ∀ ω, K ω ≤ x)
    (w : ℝ → ℝ) (hw_affine : ∀ y, 0 ≤ y → w y = 1 + y) :
    ∀ ω (t : ℝ≥0),
      rightLimit (fun s ω => if s = 0 then 0 else K ω) t ω -
          (if t = 0 then 0 else K ω) ≤
        w (riskProcess X x (fun s ω => if s = 0 then 0 else K ω) t ω) -
          w (riskProcess X x (fun s ω => if s = 0 then 0 else K ω) t ω -
            (rightLimit (fun s ω => if s = 0 then 0 else K ω) t ω -
              (if t = 0 then 0 else K ω))) := by
  intro ω t
  have hrl := avram_e0_initial_only_dividend_rightlimit K ω t
  by_cases ht : t = 0
  · subst t
    have hx : 0 ≤ x := (hKnonneg ω).trans (hKle ω)
    have hxK : 0 ≤ x - K ω := sub_nonneg.mpr (hKle ω)
    have hruin :
        riskProcess X x (fun s ω => if s = 0 then 0 else K ω) 0 ω = x := by
      simp [riskProcess, X.X_zero ω]
    simpa [hrl, hruin, hw_affine x hx,
      hw_affine (x - K ω) hxK] using (le_refl (K ω))
  · rw [hrl]
    simp [ht]
