-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_ruin_min_liminf_clock_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:19:58.792892+00:00
-- url     : https://prove2.me/submissions/ad896c53-e5b7-469b-b967-694164074fba

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤) :
    ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ,
        min (ruinTime X x D ω) (S (n + k) ω)) =
        ruinTime X x D ω := by
  filter_upwards [hSliminfAE] with ω hω
  let r : ℝ≥0∞ := ruinTime X x D ω
  have htail (n : ℕ) :
      (⨅ k : ℕ, min r (S (n + k) ω)) =
        min r (⨅ k : ℕ, S (n + k) ω) := by
    apply le_antisymm
    · apply le_inf
      · exact (iInf_le (fun k : ℕ => min r (S (n + k) ω)) 0).trans
          (min_le_left r (S (n + 0) ω))
      · refine le_iInf (fun k => ?_)
        exact (iInf_le (fun j : ℕ => min r (S (n + j) ω)) k).trans
          (min_le_right r (S (n + k) ω))
    · refine le_iInf (fun k => ?_)
      exact min_le_min_left r
        (iInf_le (fun j : ℕ => S (n + j) ω) k)
  calc
    (⨆ n : ℕ, ⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω)) =
        (⨆ n : ℕ, min r (⨅ k : ℕ, S (n + k) ω)) := by
          apply iSup_congr
          intro n
          change (⨅ k : ℕ, min r (S (n + k) ω)) =
            min r (⨅ k : ℕ, S (n + k) ω)
          exact htail n
    _ = min r (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) := by
      rw [inf_iSup_eq]
    _ = ruinTime X x D ω := by simp [r, hω]
end
