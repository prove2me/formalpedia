-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_candidate_borel_and_postPayment_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:47:43.04754+00:00
-- url     : https://prove2.me/submissions/0a5e7871-fdc7-416a-8561-e7703f2fec55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    Measurable w ∧
      Adapted 𝓕.rightCont
        (fun t ω => w (x + X.X t ω - rightLimit D t ω)) := by
  classical
  have hp : Measurable ((Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ))) :=
    hw_cont.measurable_piecewise continuousOn_const measurableSet_Ici
  have hident :
      ((Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ))) = w := by
    funext y
    by_cases hy : 0 ≤ y
    · simp [Set.piecewise, hy]
    · have hyneg : y < 0 := lt_of_not_ge hy
      simp [Set.piecewise, hy, hw_neg y hyneg]
  have hw : Measurable w := by simpa only [hident] using hp
  refine ⟨hw, ?_⟩
  intro t
  have hU : Measurable[𝓕.rightCont t]
      (fun ω => x + X.X t ω - rightLimit D t ω) :=
    (postPaymentReserve_cadlag_adapted X x D hD).2.2 t
  exact hw.comp hU
