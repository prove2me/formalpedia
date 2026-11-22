-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_abstract_charged_mesh_L1_to_expected_positive_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:32:57.549473+00:00
-- url     : https://prove2.me/submissions/5639c1f1-2dbd-419c-ab3e-26f71cfaad8d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB22_abstract_L1_positive_excess_to_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_gb25_abstract_positive_part_event_L1_transfer
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A genuine original stopped-mesh charged positive residual tending to zero
and L1 convergence of its centred source give the expected fixed-band budget. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (F N Occ : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hI : IntegrableOn
      (fun ω => max (F ω - N ω - (B + c * Occ ω)) 0) A P)
    (hMI : ∀ m, IntegrableOn
      (fun ω => max (F ω - M m ω - (B + c * Occ ω)) 0) A P)
    (hDI : ∀ m, IntegrableOn (fun ω => |N ω - M m ω|) A P)
    (hL1 : Tendsto (fun m =>
      ∫ ω in A, |N ω - M m ω| ∂P) atTop (𝓝 (0 : ℝ)))
    (hR : Tendsto (fun m =>
      ∫ ω in A, max (F ω - M m ω - (B + c * Occ ω)) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hFI : ∀ m, IntegrableOn (fun ω => max (F ω - M m ω) 0) A P)
    (hOccI : IntegrableOn Occ A P)
    (hOccNonneg : ∀ᵐ ω ∂(P.restrict A), 0 ≤ Occ ω) :
    ∀ ε : ℝ, 0 < ε → ∀ K : ℕ, ∃ m : ℕ, K < m ∧
      (∫ ω in A, max (F ω - M m ω) 0 ∂P) ≤
        B + c * (∫ ω in A, Occ ω ∂P) + ε := by
  have hPath : ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ N ω + B + c * Occ ω := by
    have h :=
      avram_gbB22_abstract_L1_positive_excess_to_ae_bound
        P A F N (fun ω => B + c * Occ ω) M
        hI hMI hDI hL1 hR
    simpa only [add_assoc] using h
  exact avram_gb25_abstract_positive_part_event_L1_transfer
    P A F N Occ M B c hB hc hFI hOccI hDI
    hOccNonneg hPath hL1

