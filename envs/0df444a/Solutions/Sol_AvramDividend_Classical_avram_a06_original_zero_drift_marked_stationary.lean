-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_zero_drift_marked_stationary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:22:08.322282+00:00
-- url     : https://prove2.me/submissions/e74c565e-1ce4-4a98-be35-e8f560657ad2

import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_marked_band_stationary
import Theorems.Thm_AvramDividend_Classical_avram_a06_piecewisePath_increment_band
import Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
import Theorems.Thm_levy_foundations_jumpCountLtIff
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
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    HasStationaryIncrements
      (fun (t : ℝ≥0) ω =>
        LevyFoundations.piecewisePath 0 0
          (fun n => LevyFoundations.arrival τ n ω)
          (fun n => Y n ω) (t : ℝ)) P := by
  intro s k
  let T := fun (ω : (ℕ → ℝ) × (ℕ → ℝ)) (j : ℕ) =>
    LevyFoundations.arrival τ j ω
  let X := fun (t : ℝ≥0) (ω : (ℕ → ℝ) × (ℕ → ℝ)) =>
    LevyFoundations.piecewisePath 0 0 (T ω) (fun j => Y j ω) (t : ℝ)
  let BS := fun ω => ∑ j ∈ Finset.Ico
      (LevyFoundations.jumpCount (T ω) (s : ℝ))
      (LevyFoundations.jumpCount (T ω) (s + k : ℝ)), Y j ω
  let B0 := fun ω => ∑ j ∈ Finset.Ico
      (LevyFoundations.jumpCount (T ω) (0 : ℝ))
      (LevyFoundations.jumpCount (T ω) (k : ℝ)), Y j ω
  have hmono : ∀ᵐ ω ∂P, Monotone (LevyFoundations.jumpCount (T ω)) := by
    filter_upwards
      [levy_foundations_compoundDriverArrivalStrictMono hd (by norm_num),
       levy_foundations_compoundDriverArrivalDiverges hd (by norm_num)]
      with ω hstrict hdiv
    intro a b hab
    by_contra hcon
    push_neg at hcon
    have h1 : T ω (LevyFoundations.jumpCount (T ω) b) ≤ a :=
      (levy_foundations_jumpCountLtIff (T ω) hstrict hdiv
        (LevyFoundations.jumpCount (T ω) b) a).mp hcon
    exact (lt_irrefl _)
      ((levy_foundations_jumpCountLtIff (T ω) hstrict hdiv
        (LevyFoundations.jumpCount (T ω) b) b).mpr (h1.trans hab))
  have hleft : (fun ω => ProbabilityTheory.increment X s (s + k) ω) =ᵐ[P] BS := by
    filter_upwards [hmono] with ω hm
    have hle : (s : ℝ) ≤ (s + k : ℝ) := by
      exact_mod_cast (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ k from bot_le))
    have hc := hm hle
    simpa [X, BS, T, ProbabilityTheory.increment, Pi.sub_apply,
      NNReal.coe_add] using
      (avram_a06_piecewisePath_increment_band 0 (T ω) (fun j => Y j ω)
        (s : ℝ) (s + k : ℝ) hc)
  have hright : (fun ω => ProbabilityTheory.increment X 0 k ω) =ᵐ[P] B0 := by
    filter_upwards [hmono] with ω hm
    have hle : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hc := hm hle
    simpa [X, B0, T, ProbabilityTheory.increment, Pi.sub_apply] using
      (avram_a06_piecewisePath_increment_band 0 (T ω) (fun j => Y j ω)
        (0 : ℝ) (k : ℝ) hc)
  have hband := avram_a06_original_marked_band_stationary P τ Y hd s k
  have hL := (IdentDistrib.of_ae_eq hband.aemeasurable_fst hleft.symm).symm
  have hR := IdentDistrib.of_ae_eq hband.aemeasurable_snd hright.symm
  exact (hL.trans hband).trans hR