-- Prove2me | solution 2 for AvramDividend.Classical.avram_a06_original_zero_drift_marked_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:34:27.962614+00:00
-- url     : https://prove2.me/submissions/3fb4569f-ee95-4b4c-bd2a-31adb6021728

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_marked_band_independent
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
    HasIndependentIncrements
      (fun (t : ℝ≥0) ω =>
        LevyFoundations.piecewisePath 0 0
          (fun n => LevyFoundations.arrival τ n ω)
          (fun n => Y n ω) (t : ℝ)) P := by
  intro n t ht
  let T := fun (ω : (ℕ → ℝ) × (ℕ → ℝ)) (j : ℕ) =>
    LevyFoundations.arrival τ j ω
  let X := fun (u : ℝ≥0) (ω : (ℕ → ℝ) × (ℕ → ℝ)) =>
    LevyFoundations.piecewisePath 0 0 (T ω) (fun j => Y j ω) (u : ℝ)
  let B := fun (i : Fin n) (ω : (ℕ → ℝ) × (ℕ → ℝ)) =>
    ∑ j ∈ Finset.Ico
      (LevyFoundations.jumpCount (T ω) (t i.castSucc : ℝ))
      (LevyFoundations.jumpCount (T ω) (t i.succ : ℝ)), Y j ω
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
  have heq (i : Fin n) :
      (fun ω => ProbabilityTheory.increment X (t i.castSucc) (t i.succ) ω)
        =ᵐ[P] B i := by
    filter_upwards [hmono] with ω hm
    have htime : (t i.castSucc : ℝ) ≤ (t i.succ : ℝ) := by
      exact_mod_cast ht (Fin.castSucc_le_succ i)
    have hc := hm htime
    simpa [X, B, T, ProbabilityTheory.increment, Pi.sub_apply] using
      (avram_a06_piecewisePath_increment_band 0 (T ω) (fun j => Y j ω)
        (t i.castSucc : ℝ) (t i.succ : ℝ) hc)
  have hband := avram_a06_original_marked_band_independent P τ Y hd n t ht
  exact hband.congr (fun i => (heq i).symm)