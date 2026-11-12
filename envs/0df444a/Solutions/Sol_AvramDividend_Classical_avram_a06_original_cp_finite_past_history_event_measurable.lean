-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_finite_past_history_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:31:41.441416+00:00
-- url     : https://prove2.me/submissions/5f48bb16-8570-4c00-b431-78b8747fb117

import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_finite_grid_count_increment_measurable
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Past grid atoms are measurable in the full observed count history. -/
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
  classical
  intro n t ht j v
  let N (ω : (ℕ → ℝ) × (ℕ → ℝ)) (u : ℝ) :=
    LevyFoundations.jumpCount (fun q => LevyFoundations.arrival τ q ω) u
  let clock : ℝ := t j.castSucc
  let H : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {ω | ∀ i : Fin n, i < j →
      N ω (t i.succ : ℝ) - N ω (t i.castSucc : ℝ) = v i}
  let past : ((ℕ → ℝ) × (ℕ → ℝ)) → Set.Iic clock → ℕ :=
    fun ω s => N ω (s : ℝ)
  let 𝓖 : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ)) :=
    MeasurableSpace.comap past inferInstance
  have hpast : Measurable[𝓖] past := measurable_iff_comap_le.mpr le_rfl
  have hmeas := AvramDividend.Classical.avram_a06_original_cp_finite_grid_count_increment_measurable
    P τ Y hd n t ht
  have hidx (i : Fin n) (hi : i < j) :
      (i.succ : Fin (n + 1)) ≤ j.castSucc := by
    change i.val + 1 ≤ j.val
    omega
  have hsub (i : Fin n) (hi : i < j) :
      Measurable[𝓖] (fun ω => N ω (t i.succ : ℝ) -
        N ω (t i.castSucc : ℝ)) := by
    have hb : (i.castSucc : Fin (n + 1)) ≤ j.castSucc := by
      change i.val ≤ j.val
      omega
    let a : Set.Iic clock :=
      ⟨(t i.succ : ℝ), by exact_mod_cast ht (hidx i hi)⟩
    let b : Set.Iic clock :=
      ⟨(t i.castSucc : ℝ), by exact_mod_cast ht hb⟩
    have hpair : Measurable (fun f : Set.Iic clock → ℕ => (f a, f b)) :=
      (measurable_pi_apply a).prodMk (measurable_pi_apply b)
    have hnat : Measurable (fun z : ℕ × ℕ => z.1 - z.2) :=
      measurable_of_countable _
    have hcomp : Measurable (fun f : Set.Iic clock → ℕ => f a - f b) :=
      hnat.comp hpair
    exact hcomp.comp hpast
  constructor
  · rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i < j
    · simpa [hi, N, Set.preimage, Set.mem_singleton_iff] using
        (measurableSet_singleton (v i)).preimage (hmeas i)
    · simp [hi]
  · change MeasurableSet[𝓖] {ω | ∀ (i : Fin n), i < j →
      N ω (t i.succ : ℝ) - N ω (t i.castSucc : ℝ) = v i}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i < j
    · simpa [hi, Set.preimage, Set.mem_singleton_iff] using
        (measurableSet_singleton (v i)).preimage (hsub i hi)
    · simp [hi]
