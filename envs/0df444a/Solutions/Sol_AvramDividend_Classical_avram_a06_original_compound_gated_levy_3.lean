-- Prove2me | solution 3 for AvramDividend.Classical.avram_a06_original_compound_gated_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:37:12.693143+00:00
-- url     : https://prove2.me/submissions/ac1c4a60-8241-47b6-9088-4130282c6ae5

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_gated_independent_increments
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_gated_stationary_increments
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoissonCadlagAE_public
import Theorems.Thm_isCadlag_comp_nnrealCoe
import Theorems.Thm_ProbabilityTheory_isCadlag_const

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

/-- The gated original source is Lévy once the two original-space
increment laws are certified; cadlag and zero-start need no new laws. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (G : Set ((ℕ → ℝ) × (ℕ → ℝ)))
    [DecidablePred (fun ω => ω ∈ G)]
    (hGmeas : MeasurableSet G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hGzero : ∀ ω ∈ G,
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y 0 ω = 0) :
    IsLevyProcess
      (fun (t : ℝ≥0) ω =>
        if ω ∈ G then LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω
        else (0 : ℝ)) P := by
  let Z : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun t ω => if ω ∈ G then
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω else 0
  have hcad : ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => Z t ω) := by
    filter_upwards
      [avram_a06_compoundPoissonCadlagAE_public hd (by norm_num) (1 : ℝ)]
      with ω hpath
    by_cases hw : ω ∈ G
    · simpa [Z, hw] using (isCadlag_comp_nnrealCoe hpath)
    · simpa [Z, hw] using
        (isCadlag_const : IsCadlag (fun _ : ℝ≥0 => (0 : ℝ)))
  refine ⟨?_, ?_, ?_, hcad⟩
  · funext ω
    by_cases hw : ω ∈ G
    · simpa [Z, hw] using hGzero ω hw
    · simp [Z, hw]
  · exact avram_a06_original_compound_gated_independent_increments
      P τ Y hd G hGmeas hGae
  · exact avram_a06_original_compound_gated_stationary_increments
      P τ Y hd G hGmeas hGae
