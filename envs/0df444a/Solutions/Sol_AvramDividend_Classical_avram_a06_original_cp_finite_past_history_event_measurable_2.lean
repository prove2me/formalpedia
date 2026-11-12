-- Prove2me | solution 2 for AvramDividend.Classical.avram_a06_original_cp_finite_past_history_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:31:44.838827+00:00
-- url     : https://prove2.me/submissions/ef5d46c7-0ffb-43a7-9c5e-33ce775bea6b

import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_finite_grid_count_increment_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a06_past_count_atom_raw_times_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Each original count-prefix atom is measurable both on the source and through its stopped count history. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t)
      (j : Fin n) (v : Fin n → ℕ),
      let N (ω : (ℕ → ℝ) × (ℕ → ℝ)) (u : ℝ) :=
        LevyFoundations.jumpCount (fun q => LevyFoundations.arrival τ q ω) u
      let clock : ℝ := t j.castSucc
      let H : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
        {ω | ∀ i : Fin n, i < j →
          N ω (t i.succ : ℝ) - N ω (t i.castSucc : ℝ) = v i}
      MeasurableSet H ∧
        MeasurableSet[
          MeasurableSpace.comap
            (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
              fun s : Set.Iic clock => N ω (s : ℝ))
            (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H := by
  intro n t ht j v
  dsimp
  let N (ω : (ℕ → ℝ) × (ℕ → ℝ)) (u : ℝ) :=
    LevyFoundations.jumpCount (fun q => LevyFoundations.arrival τ q ω) u
  let clock : ℝ := t j.castSucc
  let H : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {ω | ∀ i : Fin n, i < j →
      N ω (t i.succ : ℝ) - N ω (t i.castSucc : ℝ) = v i}
  change MeasurableSet H ∧ MeasurableSet[
    MeasurableSpace.comap
      (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
        fun s : Set.Iic clock => N ω (s : ℝ))
      (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H
  have hZi (i : Fin n) :
      Measurable (fun ω => N ω (t i.succ : ℝ) - N ω (t i.castSucc : ℝ)) :=
    AvramDividend.Classical.avram_a06_original_cp_finite_grid_count_increment_measurable
      P τ Y hd n t ht i
  have hH : MeasurableSet H := by
    have hEq : H = (⋂ i : Fin n,
        {ω | i < j → N ω (t i.succ : ℝ) - N ω (t i.castSucc : ℝ) = v i}) := by
      ext ω
      simp [H]
    rw [hEq]
    refine MeasurableSet.iInter ?_
    intro i
    by_cases hi : i < j
    · simp only [hi, true_implies]
      change MeasurableSet ((fun ω =>
        N ω (t i.succ : ℝ) - N ω (t i.castSucc : ℝ)) ⁻¹' {v i})
      exact (hZi i) (measurableSet_singleton (v i))
    · simp [hi]
  have ha : ∀ i : Fin n, i < j → (t i.castSucc : ℝ) ≤ clock := by
    intro i hi
    have hle : i.castSucc ≤ j.castSucc := by
      change i.val ≤ j.val
      exact (Fin.lt_def.mp hi).le
    exact_mod_cast ht hle
  have hb : ∀ i : Fin n, i < j → (t i.succ : ℝ) ≤ clock := by
    intro i hi
    have hle : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      omega
    exact_mod_cast ht hle
  exact ⟨hH,
    AvramDividend.Classical.avram_a06_past_count_atom_raw_times_measurable
      N clock n (fun i => (t i.castSucc : ℝ)) (fun i => (t i.succ : ℝ))
      j v ha hb⟩
