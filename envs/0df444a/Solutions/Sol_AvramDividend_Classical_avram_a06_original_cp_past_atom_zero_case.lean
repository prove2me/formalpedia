-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_past_atom_zero_case
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:58:18.503902+00:00
-- url     : https://prove2.me/submissions/a1c24ef2-7b0b-4992-adfb-435b0a9a6b67

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_threshold_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_driver_interarrival_independent
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_time_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_finite_past_history_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a06_zero_future_factor_from_ae_history
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- A finite pre-clock count atom is independent of the next zero-count increment. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      let Z : Fin n → ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ :=
        fun i ω => LevyFoundations.jumpCount
          (fun q => LevyFoundations.arrival τ q ω) (t i.succ : ℝ) -
        LevyFoundations.jumpCount
          (fun q => LevyFoundations.arrival τ q ω) (t i.castSucc : ℝ)
      ∀ (j : Fin n) (v : Fin n → ℕ),
        P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = 0} =
          P {ω | ∀ i : Fin n, i < j → Z i ω = v i} *
          P {ω | Z j ω = 0} := by
  intro n t ht
  dsimp
  intro j v
  let N (ω : (ℕ → ℝ) × (ℕ → ℝ)) (u : ℝ) :=
    LevyFoundations.jumpCount (fun q => LevyFoundations.arrival τ q ω) u
  let clock : ℝ := t j.castSucc
  let delta : ℝ := (t j.succ : ℝ) - clock
  let H : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {ω | ∀ i : Fin n, i < j →
      N ω (t i.succ : ℝ) - N ω (t i.castSucc : ℝ) = v i}
  have hclock : 0 ≤ clock := by exact_mod_cast (t j.castSucc).property
  have hdelta : 0 ≤ delta := by
    dsimp [delta, clock]
    apply sub_nonneg.mpr
    have hle : j.castSucc ≤ j.succ := by
      change j.val ≤ j.val + 1
      omega
    exact_mod_cast ht hle
  have hClock : clock + delta = (t j.succ : ℝ) := by
    dsimp [delta]
    ring
  have hN : Measurable (fun ω => N ω clock) :=
    AvramDividend.Classical.avram_a06_original_cp_count_time_measurable
      P τ Y hd clock
  have hHistory :=
    AvramDividend.Classical.avram_a06_original_cp_finite_past_history_event_measurable
      P τ Y hd n t ht j v
  have hH : MeasurableSet H := hHistory.1
  have hPast : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
          fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H := hHistory.2
  have hTau (i : ℕ) : Measurable (τ i) := hd.measurable_interarrival i
  have hIid := AvramDividend.Classical.avram_a06_original_compound_driver_interarrival_independent
    P τ Y hd
  have hExp (i : ℕ) : HasLaw (τ i) (expMeasure 1) P :=
    hd.law_interarrival i
  have hThreshold := AvramDividend.Classical.avram_a06_original_cp_count_threshold_ae
    P τ Y hd
  have hFactor :=
    AvramDividend.Classical.avram_a06_zero_future_factor_from_ae_history
      (P := P) τ hTau hIid hExp N hThreshold
      clock hclock hN H hH hPast delta hdelta
  have hUniv :=
    AvramDividend.Classical.avram_a06_zero_future_factor_from_ae_history
      (P := P) τ hTau hIid hExp N hThreshold
      clock hclock hN Set.univ MeasurableSet.univ MeasurableSet.univ delta hdelta
  have hFactor' :
      P {ω | ω ∈ H ∧ N ω (t j.succ : ℝ) - N ω clock = 0} =
        P H * ENNReal.ofReal (Real.exp (-delta)) := by
    simpa only [hClock] using hFactor
  have hUniv' :
      P {ω | N ω (t j.succ : ℝ) - N ω clock = 0} =
        ENNReal.ofReal (Real.exp (-delta)) := by
    simpa [hClock] using hUniv
  change P {ω | ω ∈ H ∧ N ω (t j.succ : ℝ) - N ω clock = 0} =
    P H * P {ω | N ω (t j.succ : ℝ) - N ω clock = 0}
  rw [hFactor', hUniv']
