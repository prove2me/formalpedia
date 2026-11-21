-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_finitecap_centered_pathwise_strip_release
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:26:28.846735+00:00
-- url     : https://prove2.me/submissions/d235a418-f6e4-44f9-b7c0-5deb987f905b

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → ℝ) (K : ℝ) (M R : ℕ → Ω → ℝ) (Γ : ℕ → ℝ)
    (hFI : Integrable F P) (hMI : ∀ j, Integrable (M j) P)
    (hM0 : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hRI : ∀ j, Integrable (R j) P)
    (hΓ : Tendsto Γ atTop (𝓝 (0 : ℝ)))
    (hR : Tendsto (fun j => ∫ ω, R j ω ∂P) atTop (𝓝 (0 : ℝ)))
    (hLedger : ∀ j, ∀ᵐ ω ∂P,
       F ω ≤ K + M j ω + Γ j + R j ω) :
    (∫ ω, F ω ∂P) ≤ K := by
  have hBound (j : ℕ) :
      (∫ ω, F ω ∂P) ≤ K + Γ j + (∫ ω, R j ω ∂P) := by
    have hC : Integrable (fun _ : Ω => K) P := integrable_const K
    have hCG : Integrable (fun _ : Ω => K + Γ j) P :=
      integrable_const _
    have hCM : Integrable (fun ω => K + M j ω) P :=
      hC.add (hMI j)
    have hCMG : Integrable (fun ω => K + M j ω + Γ j) P :=
      hCM.add (integrable_const (Γ j))
    have hAll : Integrable
        (fun ω => K + M j ω + Γ j + R j ω) P :=
      hCMG.add (hRI j)
    have hc : (∫ ω, F ω ∂P) ≤
        ∫ ω, K + M j ω + Γ j + R j ω ∂P :=
      integral_mono_ae hFI hAll (hLedger j)
    have heq : (∫ ω, K + M j ω + Γ j + R j ω ∂P) =
        K + Γ j + ∫ ω, R j ω ∂P := by
      rw [integral_add hCMG (hRI j)]
      have hCMG' : (fun ω : Ω => K + M j ω + Γ j) =
          (fun ω => (K + Γ j) + M j ω) := by
        funext ω; ring
      rw [hCMG', integral_add hCG (hMI j)]
      simp [hM0 j]
    rwa [heq] at hc
  have hUpper : Tendsto
      (fun j => K + Γ j + (∫ ω, R j ω ∂P))
      atTop (𝓝 K) := by
    convert (tendsto_const_nhds.add hΓ).add hR using 1 <;> simp
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hUpper
    (Filter.Eventually.of_forall hBound)
