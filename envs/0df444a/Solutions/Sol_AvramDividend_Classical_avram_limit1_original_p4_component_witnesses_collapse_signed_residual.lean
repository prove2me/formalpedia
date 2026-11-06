-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_original_p4_component_witnesses_collapse_signed_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:41:45.071186+00:00
-- url     : https://prove2.me/submissions/bbaf8fae-4c0c-4145-8baa-ccb39d35e991

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical

/-- Collapses original P4 Gaussian, small and large jump centred terms;
    drops the nonpositive unintegrable remainder without an L1 assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (wInit : ℝ) (Cash Term : Ω → ℝ)
    (hSource : ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        wInit + Mc ω + Ms ω + Ml ω + G ω + R ω)) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ wInit + M ω + G ω + H ω) := by
  obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI, hGI,
    hMcMean, hMsMean, hMlMean, hGSign, hRSign, hBudget⟩ := hSource
  have hMI : Integrable (Mc + Ms + Ml) P := (hMcI.add hMsI).add hMlI
  have hZI : Integrable (0 : Ω → ℝ) P := integrable_zero Ω ℝ P
  have hMMean : (∫ ω, (Mc + Ms + Ml) ω ∂P) = 0 := by
    have hSplit1 :
        (∫ ω, (Mc + Ms + Ml) ω ∂P) =
          (∫ ω, (Mc + Ms) ω ∂P) + (∫ ω, Ml ω ∂P) :=
      integral_add (hMcI.add hMsI) hMlI
    have hSplit2 :
        (∫ ω, (Mc + Ms) ω ∂P) =
          (∫ ω, Mc ω ∂P) + (∫ ω, Ms ω ∂P) :=
      integral_add hMcI hMsI
    calc
      (∫ ω, (Mc + Ms + Ml) ω ∂P) =
          (∫ ω, (Mc + Ms) ω ∂P) + (∫ ω, Ml ω ∂P) := hSplit1
      _ = ((∫ ω, Mc ω ∂P) + (∫ ω, Ms ω ∂P)) +
          (∫ ω, Ml ω ∂P) := by rw [hSplit2]
      _ = 0 := by rw [hMcMean, hMsMean, hMlMean]; norm_num
  refine ⟨Mc + Ms + Ml, G, 0, hMI, hGI, hZI, hMMean, ?_, ?_⟩
  · filter_upwards [hGSign] with ω hG
    simpa using hG
  · filter_upwards [hBudget, hRSign] with ω hB hR
    change Term ω + Cash ω ≤
      wInit + (Mc ω + Ms ω + Ml ω) + G ω + 0
    linarith only [hB, hR]
