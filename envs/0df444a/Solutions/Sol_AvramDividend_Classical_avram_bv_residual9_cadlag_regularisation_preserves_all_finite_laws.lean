-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_cadlag_regularisation_preserves_all_finite_laws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:59:11.648202+00:00
-- url     : https://prove2.me/submissions/1d1dbaff-2803-4702-bff1-9f6066ddc45e

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen16_gate_ae_cadlag_paths_to_all_paths
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (G : Set Ω)
    (hGmeas : MeasurableSet G) (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hMeas : ∀ t, Measurable (X t))
    (hCad : ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => X t ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, IsCadlag (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[P] X t) ∧
      (∀ (n : ℕ) (u : Fin n → ℝ≥0),
        P.map (fun ω => fun i : Fin n => Y (u i) ω) =
          P.map (fun ω => fun i : Fin n => X (u i) ω)) := by
  obtain ⟨Y, hYcad, hYmeas, hYae⟩ :=
    avram_gen16_gate_ae_cadlag_paths_to_all_paths
      P X G hGmeas hGae hMeas hCad
  refine ⟨Y, hYcad, hYmeas, hYae, ?_⟩
  intro n u
  have hEq : ∀ᵐ ω ∂P, ∀ i : Fin n, Y (u i) ω = X (u i) ω :=
    Filter.eventually_all.mpr (fun i => hYae (u i))
  exact Measure.map_congr (hEq.mono (fun ω hω => funext hω))
