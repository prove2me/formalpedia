-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_centered_physical_mesh_mean_budget_from_vanishing_signed_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:43:02.21241+00:00
-- url     : https://prove2.me/submissions/e34b7fe5-a354-4a52-9c16-668767ce67d6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter

/-- Original finite-grid centred Gaussian gains plus vanishing signed physical mesh error bound the stopped expected reward. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : Ω → ℝ) (M E : ℕ → Ω → ℝ)
    (K : ℝ)
    (hFI : Integrable F P)
    (hMI : ∀ j, Integrable (M j) P)
    (hMean : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hEI : ∀ j, Integrable (E j) P)
    (hErr : Tendsto (fun j => ∫ ω, E j ω ∂P)
      Filter.atTop (nhds (0 : ℝ)))
    (hLedger : ∀ j, ∀ᵐ ω ∂P,
      F ω ≤ K + M j ω + E j ω) :
    (∫ ω, F ω ∂P) ≤ K  := by
  have hBound (j : ℕ) :
      (∫ ω, F ω ∂P) ≤ K + (∫ ω, E j ω ∂P) := by
    have hK : Integrable (fun _ : Ω => K) P :=
      integrable_const K
    have hKM : Integrable (fun ω => K + M j ω) P :=
      hK.add (hMI j)
    have hKME : Integrable (fun ω => K + M j ω + E j ω) P :=
      hKM.add (hEI j)
    have hComp :
        (∫ ω, F ω ∂P) ≤
          (∫ ω, K + M j ω + E j ω ∂P) :=
      integral_mono_ae hFI hKME (hLedger j)
    have hIntegral :
        (∫ ω, K + M j ω + E j ω ∂P) =
          K + (∫ ω, E j ω ∂P) := by
      rw [integral_add hKM (hEI j), integral_add hK (hMI j)]
      simp [Measure.real, hMean j]
    rw [hIntegral] at hComp
    exact hComp
  have hLimit : Tendsto
      (fun j => K + (∫ ω, E j ω ∂P))
      Filter.atTop (nhds K) := by
    convert (tendsto_const_nhds.add hErr) using 1 <;> simp
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hLimit
    (Filter.Eventually.of_forall hBound)
