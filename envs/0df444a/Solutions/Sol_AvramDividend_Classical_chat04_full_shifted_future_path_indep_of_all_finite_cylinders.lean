-- Prove2me | solution 1 for AvramDividend.Classical.chat04_full_shifted_future_path_indep_of_all_finite_cylinders
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:45:19.724643+00:00
-- url     : https://prove2.me/submissions/9f353375-ad6a-4627-acf2-bd47778b61e4

import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Full continuous-time future-path independence from an arbitrary statistic
of past history. The sole remaining stochastic premise is joint independence
of each finite cylinder from H, which is strictly stronger than each
coordinate's individual independence. Mathlib promotes those cylinders
to the function-valued process without a countability assumption.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (hFinite : ∀ I : Finset ℝ≥0,
      IndepFun
        (fun ω (i : I) => X.X (s + (i : ℝ≥0)) ω - X.X s ω)
        H P) :
    IndepFun
      (fun ω (t : ℝ≥0) => X.X (s + t) ω - X.X s ω)
      H P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : ℝ≥0 → Ω → ℝ :=
    fun t ω => X.X (s + t) ω - X.X s ω
  have hY : ∀ t, Measurable (Y t) := by
    intro t
    dsimp [Y]
    have ht : Measurable (X.X (s + t)) :=
      (X.adapted (s + t)).mono (𝓕.le (s + t)) le_rfl
    have hs : Measurable (X.X s) :=
      (X.adapted s).mono (𝓕.le s) le_rfl
    exact ht.sub hs
  have hHm : Measurable H := hH.mono (𝓕.le s) le_rfl
  have hCylinder : ∀ I : Finset ℝ≥0,
      IndepFun (fun ω (i : I) => Y i.val ω) H P := by
    intro I
    simpa only [Y] using hFinite I
  have hProcess : IndepFun (fun ω t => Y t ω) H P :=
    IndepFun.process_indepFun hY hHm hCylinder
  simpa only [Y] using hProcess
