-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_L1_signed_witness_iff_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:23:33.014336+00:00
-- url     : https://prove2.me/submissions/12ec0c33-7b4d-4eb4-a2d4-ebac5864cde2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the original probability law and for integrable true stopped cash
    and terminal, the signed residual witness is equivalent to its budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ)
    (Term Cash : Ω → ℝ)
    (hTermI : Integrable Term P) (hCashI : Integrable Cash P) :
    (∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) ↔
    ((∫ ω, Term ω + Cash ω ∂P) ≤ w x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  constructor
  · rintro ⟨M, G, H, hMI, hGI, hHI, hMean, hSign, hPath⟩
    have hS : Integrable (fun ω => Term ω + Cash ω) P :=
      hTermI.add hCashI
    have hR : Integrable
        (fun ω => w x + M ω + G ω + H ω) P :=
      (((integrable_const (w x)).add hMI).add hGI).add hHI
    have hLe :=
      integral_mono_ae hS hR hPath
    have hNeg : (∫ ω, G ω + H ω ∂P) ≤ 0 :=
      integral_nonpos_of_ae hSign
    rw [integral_add hGI hHI] at hNeg
    have hRight :
        (∫ ω, w x + M ω + G ω + H ω ∂P) =
        w x + (∫ ω, M ω ∂P) +
          (∫ ω, G ω ∂P) + (∫ ω, H ω ∂P) := by
      simp [integral_add, hMI, hGI, hHI]
    rw [hRight, hMean] at hLe
    linarith
  · intro hBudget
    exact avram_p4_f_assembly_expected_budget_witness_of_original_L1
      X w x Term Cash hTermI hCashI hBudget
