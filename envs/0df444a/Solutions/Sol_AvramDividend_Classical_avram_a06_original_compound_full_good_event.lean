-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_compound_full_good_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:41:56.620148+00:00
-- url     : https://prove2.me/submissions/8d4e264f-ce62-4d3a-97f4-58a8488c8ec6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoissonStartsZeroAE_public
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoissonCadlagAE_public
import Theorems.Thm_isCadlag_comp_nnrealCoe
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_ae_nonpositive_left_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Extract one measurable full-measure event from the original
compound-Poisson path regularity, zero-start and no-upward-jump facts. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ G : Set ((ℕ → ℝ) × (ℕ → ℝ)),
      MeasurableSet G ∧
      (∀ᵐ ω ∂P, ω ∈ G) ∧
      (∀ ω ∈ G, LevyFoundations.compoundPoisson (1 : ℝ) τ Y 0 ω = 0) ∧
      (∀ ω ∈ G, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun s : ℝ≥0 =>
          LevyFoundations.compoundPoisson (1 : ℝ) τ Y (s : ℝ) ω) (Ici t) t) ∧
      (∀ ω ∈ G, ∀ t : ℝ≥0, 0 < t →
        ∃ l, Tendsto (fun s : ℝ≥0 =>
          LevyFoundations.compoundPoisson (1 : ℝ) τ Y (s : ℝ) ω)
          (nhdsWithin t (Iio t)) (nhds l)) ∧
      (∀ ω ∈ G, ∀ t : ℝ≥0, ∀ l : ℝ, 0 < t →
        Tendsto (fun s : ℝ≥0 =>
          LevyFoundations.compoundPoisson (1 : ℝ) τ Y (s : ℝ) ω)
          (nhdsWithin t (Iio t)) (nhds l) →
        LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω ≤ l) := by
  let X : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun t ω => LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω
  let R : ((ℕ → ℝ) × (ℕ → ℝ)) → Prop := fun ω =>
    X 0 ω = 0 ∧
    (∀ t, ContinuousWithinAt (fun s => X s ω) (Ici t) t) ∧
    (∀ t, 0 < t →
      ∃ l, Tendsto (fun s => X s ω) (nhdsWithin t (Iio t)) (nhds l)) ∧
    (∀ t l, 0 < t →
      Tendsto (fun s => X s ω) (nhdsWithin t (Iio t)) (nhds l) →
      X t ω ≤ l)
  have hstart := avram_a06_compoundPoissonStartsZeroAE_public hd (by norm_num) (1 : ℝ)
  have hcad := avram_a06_compoundPoissonCadlagAE_public hd (by norm_num) (1 : ℝ)
  have hdown := avram_a06_original_compound_ae_nonpositive_left_jumps P τ Y hd
  have hR : ∀ᵐ ω ∂P, R ω := by
    filter_upwards [hstart, hcad, hdown] with ω hz hc hn
    dsimp [R]
    have hc' : IsCadlag (fun t : ℝ≥0 => X t ω) :=
      isCadlag_comp_nnrealCoe hc
    exact ⟨hz, (fun t => (hc' t).1), (fun t _ => (hc' t).2), hn⟩
  have hnull : P {ω | ¬ R ω} = 0 := (ae_iff).1 hR
  obtain ⟨N, hsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null hnull
  have hgood : ∀ ω ∈ Nᶜ, R ω := by
    intro ω hw
    by_contra hn
    exact hw (hsub hn)
  refine ⟨Nᶜ, hNmeas.compl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ae_iff).2 (by simpa using hNnull)
  · intro ω hw
    change X 0 ω = 0
    exact (hgood ω hw).1
  · intro ω hw t
    change ContinuousWithinAt (fun s => X s ω) (Ici t) t
    exact (hgood ω hw).2.1 t
  · intro ω hw t ht
    change ∃ l, Tendsto (fun s => X s ω)
      (nhdsWithin t (Iio t)) (nhds l)
    exact (hgood ω hw).2.2.1 t ht
  · intro ω hw t l ht hl
    change X t ω ≤ l
    exact (hgood ω hw).2.2.2 t l ht hl
