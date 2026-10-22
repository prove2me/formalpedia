-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_countable_path_independent_of_all_finite_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:22:20.888231+00:00
-- url     : https://prove2.me/submissions/5cd2c9e9-e393-4655-bc4c-7dd27f695a79

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Exact countable-path closure of finite-cylinder independence.
The hypothesis is uniform independence of *every finite prefix* from F_s.
It is stronger than coordinatewise independence and deliberately does
not assume independence of coordinates separately implies independence
of the whole vector. The conclusion covers arbitrary countable schedules.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hFinite : ∀ n : ℕ,
      Indep (⨆ i : Fin n, MeasurableSpace.comap
        (fun ω => X.X (s + τ i.val) ω - X.X s ω) inferInstance)
        (𝓕 s) P) :
    Indep
      (MeasurableSpace.comap
        (fun ω : Ω => fun j : ℕ => X.X (s + τ j) ω - X.X s ω)
        inferInstance)
      (𝓕 s) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let g : ℕ → Ω → ℝ :=
    fun j ω => X.X (s + τ j) ω - X.X s ω
  let m : ℕ → MeasurableSpace Ω :=
    fun n => ⨆ i : Fin n, MeasurableSpace.comap (g i.val) inferInstance
  have hg : ∀ j, Measurable (g j) := by
    intro j
    dsimp [g]
    have hXt : Measurable (X.X (s + τ j)) :=
      (X.adapted (s + τ j)).mono (𝓕.le (s + τ j)) le_rfl
    have hXs : Measurable (X.X s) :=
      (X.adapted s).mono (𝓕.le s) le_rfl
    exact hXt.sub hXs
  have hm_le : ∀ n, m n ≤ mΩ := by
    intro n
    exact iSup_le (fun i : Fin n => (hg i.val).comap_le)
  have hm_mono : Monotone m := by
    intro n k hnk
    refine iSup_le fun i : Fin n => ?_
    let j : Fin k := ⟨i.val, lt_of_lt_of_le i.isLt hnk⟩
    exact le_iSup_of_le j (le_refl _)
  have hSigma :
      (⨆ n : ℕ, m n) =
        ⨆ j : ℕ, MeasurableSpace.comap (g j) inferInstance := by
    apply le_antisymm
    · refine iSup_le fun n => ?_
      refine iSup_le fun i : Fin n => ?_
      exact le_iSup_of_le i.val (le_refl _)
    · refine iSup_le fun j => ?_
      have hstep : MeasurableSpace.comap (g j) inferInstance ≤ m (j+1) := by
        exact le_iSup_of_le (⟨j, Nat.lt_succ_self j⟩ : Fin (j+1)) (le_refl _)
      exact le_iSup_of_le (j+1) hstep
  have hIndep : Indep (⨆ n : ℕ, m n) (𝓕 s) P := by
    apply indep_iSup_of_monotone (m:=m)
      (m1:=𝓕 s) (μ:=P)
    · intro n
      simpa only [m, g] using hFinite n
    · exact hm_le
    · exact 𝓕.le s
    · exact hm_mono
  change Indep
    (MeasurableSpace.comap (fun ω => fun j : ℕ => g j ω) inferInstance)
      (𝓕 s) P
  rw [MeasurableSpace.comap_process_pi]
  rw [← hSigma]
  exact hIndep
