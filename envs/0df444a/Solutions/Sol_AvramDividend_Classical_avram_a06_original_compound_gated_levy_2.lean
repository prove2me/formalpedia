-- Prove2me | solution 2 for AvramDividend.Classical.avram_a06_original_compound_gated_levy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:54:02.677874+00:00
-- url     : https://prove2.me/submissions/12bb4b96-250e-49ba-850b-77fa8e62e2ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_raw_stationary_increments
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_raw_independent_increments
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_full_good_event
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
    (hGmeas : MeasurableSet G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hGzero : ∀ ω ∈ G,
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y 0 ω = 0) :
    IsLevyProcess (fun (t : ℝ≥0) ω =>
      if ω ∈ G then LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω else 0) P := by
  let Z : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun t ω => LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω
  let Q : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun t ω => if ω ∈ G then Z t ω else 0
  have hQ (u : ℝ≥0) : Q u =ᵐ[P] Z u := by
    filter_upwards [hGae] with ω hω
    simp [Q, hω]
  have hind : HasIndependentIncrements Q P := by
    intro n t ht
    have hr := avram_a06_original_compound_raw_independent_increments P τ Y hd n t ht
    change iIndepFun (fun (i : Fin n) ω => ProbabilityTheory.increment Z (t i.castSucc) (t i.succ) ω) P at hr
    apply hr.congr
    intro i
    filter_upwards [hQ (t i.castSucc), hQ (t i.succ)] with ω hs hk
    simp [ProbabilityTheory.increment, hk, hs]
  have hsta : HasStationaryIncrements Q P := by
    intro s k
    have hr := avram_a06_original_compound_raw_stationary_increments P τ Y hd s k
    change IdentDistrib (fun ω => ProbabilityTheory.increment Z s (s + k) ω)
      (fun ω => ProbabilityTheory.increment Z 0 k ω) P P at hr
    have hleft :
        (fun ω => ProbabilityTheory.increment Q s (s + k) ω) =ᵐ[P]
        (fun ω => ProbabilityTheory.increment Z s (s + k) ω) := by
      filter_upwards [hQ s, hQ (s + k)] with ω hs hk
      simp [ProbabilityTheory.increment, hk, hs]
    have hright :
        (fun ω => ProbabilityTheory.increment Q 0 k ω) =ᵐ[P]
        (fun ω => ProbabilityTheory.increment Z 0 k ω) := by
      filter_upwards [hQ 0, hQ k] with ω h0 hk
      simp [ProbabilityTheory.increment, hk, h0]
    have hl := (IdentDistrib.of_ae_eq hr.aemeasurable_fst hleft.symm).symm
    have hv := IdentDistrib.of_ae_eq hr.aemeasurable_snd hright.symm
    exact (hl.trans hr).trans hv
  rcases avram_a06_original_compound_full_good_event P τ Y hd with ⟨H, hHmeas, hHae, hHzero, hHright, hHleft, hHjump⟩
  have hcad : ∀ᵐ ω ∂P, IsCadlag (fun t => Q t ω) := by
    filter_upwards [hGae, hHae] with ω hg hh
    intro t
    constructor
    · simpa [Q, hg, Z] using hHright ω hh t
    · by_cases ht : t = 0
      · subst t
        refine ⟨0, ?_⟩
        have hbot : nhdsWithin (0 : ℝ≥0) (Iio 0) = ⊥ := by
          rw [show Iio (0 : ℝ≥0) = ∅ by ext x; simp]
          simp
        simp [hbot]
      · obtain ⟨l, hl⟩ := hHleft ω hh t (pos_iff_ne_zero.mpr ht)
        exact ⟨l, by simpa [Q, hg, Z] using hl⟩
  change IsLevyProcess Q P
  refine ⟨?_, hind, hsta, hcad⟩
  funext ω
  by_cases hg : ω ∈ G
  · simpa [Q, Z, hg] using hGzero ω hg
  · simp [Q, hg]
