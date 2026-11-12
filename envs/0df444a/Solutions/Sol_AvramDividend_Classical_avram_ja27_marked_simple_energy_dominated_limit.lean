-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja27_marked_simple_energy_dominated_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:32:51.73755+00:00
-- url     : https://prove2.me/submissions/120b6d29-7de2-463e-9035-972fe527f437

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A dominated original-space mark-simple squared energy converges to its
physical marked-integral squared energy. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (C g : Ω → ℝ) (E : ℕ → ℝ) (e : ℝ)
    (hMeas : ∀ k, AEStronglyMeasurable (fun ω => (F k ω) ^ 2) P)
    (hg : Integrable g P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, ‖(F k ω) ^ 2‖ ≤ g ω)
    (hLim : ∀ᵐ ω ∂P,
      Tendsto (fun k => (F k ω) ^ 2) atTop (𝓝 ((C ω) ^ 2)))
    (hSqMom : ∀ k, (∫ ω, (F k ω) ^ 2 ∂P) = E k)
    (hEnergy : Tendsto E atTop (𝓝 e)) :
    (∫ ω, (C ω) ^ 2 ∂P) = e := by
  have hInt :
      Tendsto (fun k => ∫ ω, (F k ω) ^ 2 ∂P)
        atTop (𝓝 (∫ ω, (C ω) ^ 2 ∂P)) :=
    tendsto_integral_of_dominated_convergence g hMeas hg hDom hLim
  have hExact :
      (fun k : ℕ => ∫ ω, (F k ω) ^ 2 ∂P) = E := by
    funext k
    exact hSqMom k
  rw [hExact] at hInt
  exact tendsto_nhds_unique hInt hEnergy
