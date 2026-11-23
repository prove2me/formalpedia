-- Prove2me | solution 1 for AvramDividend.Classical.avram_b59_original_B25_dominated_centered_event_mesh_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:53:14.362204+00:00
-- url     : https://prove2.me/submissions/43857c4d-b5ec-4823-8dc4-973307e0554f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A : Set Ω) (G : ℕ → Ω → ℝ) (MG BG : Ω → ℝ)
    (hGI : ∀ k, Integrable (G k) P)
    (hBG : Integrable BG P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω)
    (hLim : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hCenter : ∀ k, (∫ ω in A, G k ω ∂P) = 0) :
    (∫ ω in A, MG ω ∂P) = 0 := by
  have hGI_A (k : ℕ) :
      Integrable (G k) (P.restrict A) :=
    (hGI k).mono_measure Measure.restrict_le_self
  have hBG_A : Integrable BG (P.restrict A) :=
    hBG.mono_measure Measure.restrict_le_self
  have hDom_A (k : ℕ) :
      ∀ᵐ ω ∂P.restrict A, ‖G k ω‖ ≤ BG ω :=
    ae_restrict_of_ae (hDom k)
  have hLim_A :
      ∀ᵐ ω ∂P.restrict A,
        Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)) :=
    ae_restrict_of_ae hLim
  have hConverge :
      Tendsto (fun k => ∫ ω in A, G k ω ∂P)
        atTop (𝓝 (∫ ω in A, MG ω ∂P)) :=
    tendsto_integral_of_dominated_convergence BG
      (fun k => (hGI_A k).aestronglyMeasurable)
      hBG_A hDom_A hLim_A
  have hCentred :
      Tendsto (fun k => ∫ ω in A, G k ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    simp [hCenter]
  exact tendsto_nhds_unique hConverge hCentred
