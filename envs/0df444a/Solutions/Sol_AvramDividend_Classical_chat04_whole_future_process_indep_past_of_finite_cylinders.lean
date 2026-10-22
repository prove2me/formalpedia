-- Prove2me | solution 1 for AvramDividend.Classical.chat04_whole_future_process_indep_past_of_finite_cylinders
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:56:59.38833+00:00
-- url     : https://prove2.me/submissions/26a5aff8-a2d1-4488-8c2a-3b1ee7aebb29

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
Whole-future-process independence from the entire filtration F_s.
The assumption is finite joint cylinder sigma algebra independence from
F_s for EVERY finite set of future times, not each coordinate separately.
We close this under finite unions with the pinned monotone iSup lemma.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (hFinite : ∀ I : Finset ℝ≥0,
      Indep (⨆ t ∈ I,
        MeasurableSpace.comap
          (fun ω => X.X (s + t) ω - X.X s ω) inferInstance)
        (𝓕 s) P) :
    Indep
      (MeasurableSpace.comap
        (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
        inferInstance)
      (𝓕 s) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : ℝ≥0 → Ω → ℝ :=
    fun t ω => X.X (s + t) ω - X.X s ω
  let m : Finset ℝ≥0 → MeasurableSpace Ω :=
    fun I => ⨆ t ∈ I, MeasurableSpace.comap (Y t) inferInstance
  have hY : ∀ t, Measurable (Y t) := by
    intro t
    dsimp [Y]
    have ht : Measurable (X.X (s + t)) :=
      (X.adapted (s + t)).mono (𝓕.le (s + t)) le_rfl
    have hs : Measurable (X.X s) :=
      (X.adapted s).mono (𝓕.le s) le_rfl
    exact ht.sub hs
  have hm_le : ∀ I, m I ≤ mΩ := by
    intro I
    exact iSup_le (fun t => iSup_le (fun ht => (hY t).comap_le))
  have hm_mono : Monotone m := by
    intro I J hIJ
    dsimp [m]
    refine iSup_le fun t => iSup_le fun ht => ?_
    exact le_iSup_of_le t (le_iSup_of_le (hIJ ht) (le_refl _))
  have hSup :
      (⨆ I : Finset ℝ≥0, m I) =
        ⨆ t : ℝ≥0, MeasurableSpace.comap (Y t) inferInstance := by
    apply le_antisymm
    · refine iSup_le fun I => ?_
      dsimp [m]
      exact iSup_le (fun t => iSup_le (fun ht =>
        le_iSup_of_le t (le_refl _)))
    · refine iSup_le fun t => ?_
      have hmem : t ∈ ({t} : Finset ℝ≥0) := by simp
      have ht :
          MeasurableSpace.comap (Y t) inferInstance ≤ m {t} := by
        dsimp [m]
        exact le_iSup_of_le t (le_iSup_of_le hmem (le_refl _))
      exact le_iSup_of_le ({t} : Finset ℝ≥0) ht
  have hIndep : Indep (⨆ I : Finset ℝ≥0, m I) (𝓕 s) P := by
    apply indep_iSup_of_monotone (m:=m) (m1:=𝓕 s) (μ:=P)
    · intro I
      simpa only [m, Y] using hFinite I
    · exact hm_le
    · exact 𝓕.le s
    · exact hm_mono
  change Indep
    (MeasurableSpace.comap (fun ω t => Y t ω) inferInstance)
      (𝓕 s) P
  rw [MeasurableSpace.comap_process_pi]
  rw [← hSup]
  exact hIndep
