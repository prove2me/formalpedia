-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_eventwise_positive_excess_and_global_L1_imply_ae_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:31:41.292728+00:00
-- url     : https://prove2.me/submissions/8f2b3290-0acd-4ee1-8c53-b04c412aa681

import Theorems.Thm_AvramDividend_Classical_avram_gbB54y_positive_excess_L1_and_approximation_L1_imply_ae_upper
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (K N : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hKI : Integrable K (P.restrict A)) (hNI : Integrable N P)
    (hMI : ∀ m, Integrable (M m) P)
    (hRes : Tendsto (fun m => ∫ ω in A, max (K ω - M m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hDiff : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂P)
      atTop (nhds (0 : ℝ))) :
    ∀ᵐ ω ∂P, ω ∈ A → K ω ≤ N ω := by
  have hmono : P.restrict A ≤ P := Measure.restrict_le_self
  have hLower (m : ℕ) : 0 ≤ ∫ ω in A, |N ω - M m ω| ∂P :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hUpper (m : ℕ) : (∫ ω in A, |N ω - M m ω| ∂P) ≤
      ∫ ω, |N ω - M m ω| ∂P :=
    integral_mono_measure hmono
      (Filter.Eventually.of_forall (fun ω => abs_nonneg _)) ((hNI.sub (hMI m)).abs)
  have hLocal := tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hDiff hLower hUpper
  have hAe := avram_gbB54y_positive_excess_L1_and_approximation_L1_imply_ae_upper
    (P.restrict A) K N M hKI hNI.integrableOn (fun m => (hMI m).integrableOn)
    hRes hLocal
  exact (ae_restrict_iff' hA).mp hAe
