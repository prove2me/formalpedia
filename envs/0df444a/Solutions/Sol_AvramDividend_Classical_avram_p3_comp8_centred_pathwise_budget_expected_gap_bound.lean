-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_centred_pathwise_budget_expected_gap_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:45:33.177489+00:00
-- url     : https://prove2.me/submissions/7569580a-736c-4ce4-bf30-f47bdc97fe5b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section

/- Integrability and centring transfer an actual pathwise error budget
   to the exact signed expectation gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F B M Err : Ω → ℝ) (k : ℝ)
    (hFI : Integrable F P) (hBI : Integrable B P)
    (hMI : Integrable M P)
    (hMean : (∫ ω, M ω ∂P) = 0)
    (hEI : Integrable (fun ω => max (Err ω) 0) P)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ k + (M ω + B ω) + max (Err ω) 0) :
    max ((∫ ω, F ω ∂P) - k - (∫ ω, B ω ∂P)) 0 ≤
      (∫ ω, max (Err ω) 0 ∂P) := by
  have hMB : Integrable (fun ω => M ω + B ω) P := hMI.add hBI
  have hKMB : Integrable (fun ω => k + (M ω + B ω)) P :=
    (integrable_const k).add hMB
  have hAll :
      Integrable (fun ω => k + (M ω + B ω) + max (Err ω) 0) P :=
    hKMB.add hEI
  have hUpper :
      (∫ ω, F ω ∂P) ≤
        (∫ ω, k + (M ω + B ω) + max (Err ω) 0 ∂P) :=
    integral_mono_ae hFI hAll hBudget
  have hEval :
      (∫ ω, k + (M ω + B ω) + max (Err ω) 0 ∂P) =
        k + ((∫ ω, M ω ∂P) + (∫ ω, B ω ∂P)) +
          (∫ ω, max (Err ω) 0 ∂P) := by
    rw [integral_add hKMB hEI]
    rw [integral_add (integrable_const k) hMB]
    rw [integral_add hMI hBI]
    simp
  rw [hEval, hMean] at hUpper
  have hNonneg : 0 ≤ (∫ ω, max (Err ω) 0 ∂P) :=
    integral_nonneg (fun ω => le_max_right _ _)
  apply max_le
  · linarith
  · exact hNonneg
