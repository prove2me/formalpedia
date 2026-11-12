-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb19_two_noise_initial_event_masked_reward_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:42:28.491195+00:00
-- url     : https://prove2.me/submissions/0c977b89-3e93-4396-8355-4fc7b9cd343b

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin24_initial_event_condcentered_mask_transfer

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Combine the original-filtration centred Gaussian and compensated jump
noises while discarding a nonpositive stopped HJB/dividend remainder. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (E T : Set Ω) (hE : MeasurableSet[m] E) (hET : E ⊆ T)
    (b : ℝ) (hb : 0 ≤ b)
    (R MG MJ B : Ω → ℝ)
    (hRI : Integrable R P)
    (hMGI : Integrable MG P) (hMJI : Integrable MJ P)
    (hMG0 : P[MG | m] =ᵐ[P] 0)
    (hMJ0 : P[MJ | m] =ᵐ[P] 0)
    (hBsign : ∀ᵐ ω ∂(P.restrict E), B ω ≤ 0)
    (hLedger : ∀ᵐ ω ∂(P.restrict E),
      R ω ≤ b + MG ω + MJ ω + B ω) :
    (∫ ω in E, R ω ∂P) ≤ b * (P T).toReal := by
  have hNoiseI : Integrable (MG + MJ) P := hMGI.add hMJI
  have hNoise0 : P[MG + MJ | m] =ᵐ[P] 0 := by
    filter_upwards [condExp_add hMGI hMJI m, hMG0, hMJ0]
      with ω hsum hgauss hjump
    calc
      P[MG + MJ | m] ω = (P[MG | m] + P[MJ | m]) ω := hsum
      _ = 0 := by simp [Pi.add_apply, hgauss, hjump]
  exact @AvramDividend.Classical.avram_mix_fin24_initial_event_condcentered_mask_transfer
    Ω mΩ P inferInstance m hm E T hE hET b hb R (MG + MJ) hRI hNoiseI hNoise0
    (by
      filter_upwards [hLedger, hBsign] with ω hledger hB
      dsimp
      linarith)
