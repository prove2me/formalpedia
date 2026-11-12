-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_compound_gated_stationary_increments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:11:58.80695+00:00
-- url     : https://prove2.me/submissions/e77fd737-d689-40a8-a596-fd06cc5600e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_raw_stationary_increments
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_fixedTime_measurable_public

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (G : Set ((ℕ → ℝ) × (ℕ → ℝ)))
    [DecidablePred (fun ω => ω ∈ G)]
    (hGmeas : MeasurableSet G) (hGae : ∀ᵐ ω ∂P, ω ∈ G) :
    HasStationaryIncrements
      (fun (t : ℝ≥0) ω =>
        if ω ∈ G then LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω
        else (0 : ℝ)) P := by
  classical
  let C : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun t ω => LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω
  let Z : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun t ω => if ω ∈ G then C t ω else 0
  have hsource : HasStationaryIncrements C P :=
    avram_a06_original_compound_raw_stationary_increments P τ Y hd
  have hZm : ∀ t, Measurable (Z t) := by
    intro t
    change Measurable (fun ω => if ω ∈ G then
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω else (0 : ℝ))
    exact Measurable.ite hGmeas
      (avram_a06_compoundPoisson_fixedTime_measurable_public
        (1 : ℝ) τ Y hd.measurable_interarrival hd.measurable_mark (t : ℝ))
      measurable_const
  have hEq : ∀ t, Z t =ᵐ[P] C t := by
    intro t
    filter_upwards [hGae] with ω hw
    simp [Z, C, hw]
  intro s k
  let fs := increment Z s (s + k)
  let f0 := increment Z 0 k
  let gs := increment C s (s + k)
  let g0 := increment C 0 k
  have hs : fs =ᵐ[P] gs := by
    filter_upwards [hGae] with ω hw
    simp [fs, gs, increment, Z, C, hw]
  have hk : f0 =ᵐ[P] g0 := by
    filter_upwards [hGae] with ω hw
    simp [f0, g0, increment, Z, C, hw]
  have hmfs : AEMeasurable fs P :=
    ((hZm (s + k)).sub (hZm s)).aemeasurable
  have hmf0 : AEMeasurable f0 P :=
    ((hZm k).sub (hZm 0)).aemeasurable
  have hdist : IdentDistrib gs g0 P P := hsource s k
  change IdentDistrib fs f0 P P
  refine ⟨hmfs, hmf0, ?_⟩
  calc
    P.map fs = P.map gs := Measure.map_congr hs
    _ = P.map g0 := hdist.map_eq
    _ = P.map f0 := (Measure.map_congr hk).symm
