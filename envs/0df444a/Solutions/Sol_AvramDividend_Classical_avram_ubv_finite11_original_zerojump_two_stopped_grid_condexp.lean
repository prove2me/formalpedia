-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T09:40:55.669901+00:00
-- url     : https://prove2.me/submissions/2696d126-df46-4ce7-9c61-0912fbf657d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_monotone_clock_reindex

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Both original Gaussian source martingales obey optional sampling between
two bounded stops on the same right-continuous-filtration physical grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (grid i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (hgrid hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (grid i) } : Filtration ℕ mΩ))
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hbounded : ∀ ω, β ω ≤ (N : WithTop ℕ)) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
      (M t ω) ^ 2 - (t : ℝ) * X.σ ^ 2
    (stoppedValue (fun i : ℕ => M (grid i)) α =ᵐ[P]
      P[stoppedValue (fun i : ℕ => M (grid i)) β | hα.measurableSpace]) ∧
    (stoppedValue (fun i : ℕ => Q (grid i)) α =ᵐ[P]
      P[stoppedValue (fun i : ℕ => Q (grid i)) β | hα.measurableSpace]) := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
    (M t ω) ^ 2 - (t : ℝ) * X.σ ^ 2
  change (stoppedValue (fun i : ℕ => M (grid i)) α =ᵐ[P]
      P[stoppedValue (fun i : ℕ => M (grid i)) β | hα.measurableSpace]) ∧
    (stoppedValue (fun i : ℕ => Q (grid i)) α =ᵐ[P]
      P[stoppedValue (fun i : ℕ => Q (grid i)) β | hα.measurableSpace])
  have hm : Martingale (fun i : ℕ => M (grid i)) 𝓖 P := by
    rw [h𝓖]
    exact chat03_martingale_monotone_clock_reindex M
      (avram_wave6_03_original_rightCont_zerojump_centered_source_martingale X hν)
      grid hgrid
  have hq : Martingale (fun i : ℕ => Q (grid i)) 𝓖 P := by
    rw [h𝓖]
    exact chat03_martingale_monotone_clock_reindex Q
      (avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale X hν)
      grid hgrid
  constructor
  · exact hm.stoppedValue_ae_eq_condExp_of_le hβ hα hαβ hbounded
  · exact hq.stoppedValue_ae_eq_condExp_of_le hβ hα hαβ hbounded
