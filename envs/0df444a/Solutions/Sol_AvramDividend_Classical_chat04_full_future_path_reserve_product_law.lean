-- Prove2me | solution 1 for AvramDividend.Classical.chat04_full_future_path_reserve_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:23:33.680367+00:00
-- url     : https://prove2.me/submissions/4f932a4b-58e1-4e7e-8490-dd01da002dab

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_whole_future_process_indep_past_of_finite_cylinders

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Entire uncountable future-increment path has product joint distribution
with the reserve at s, provided uniform finite-cylinder independence from
F_s. This is the state–future-path Markov factorization at measure level.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (hFinite : ∀ I : Finset ℝ≥0,
      Indep (⨆ t ∈ I, MeasurableSpace.comap
        (fun ω => X.X (s + t) ω - X.X s ω) inferInstance)
        (𝓕 s) P) :
    Measure.map
      (fun ω => (X.X s ω,
        fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P =
      (Measure.map (X.X s) P).prod
        (Measure.map (fun ω => fun t : ℝ≥0 =>
          X.X (s + t) ω - X.X s ω) P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (s + t) ω - X.X s ω
  let R : Ω → ℝ := X.X s
  have hRm : Measurable R :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hYm : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro t
    have ht : Measurable (X.X (s + t)) :=
      (X.adapted (s + t)).mono (𝓕.le (s + t)) le_rfl
    exact ht.sub hRm
  have hFuture :
      Indep (MeasurableSpace.comap Y inferInstance) (𝓕 s) P := by
    simpa only [Y] using
      AvramDividend.Classical.chat04_whole_future_process_indep_past_of_finite_cylinders
        X s hFinite
  have hRle : MeasurableSpace.comap R inferInstance ≤ 𝓕 s :=
    (X.adapted s).comap_le
  have hIndep : Indep (MeasurableSpace.comap Y inferInstance)
      (MeasurableSpace.comap R inferInstance) P :=
    indep_of_indep_of_le_right hFuture hRle
  have hIF : IndepFun R Y P :=
    (IndepFun_iff_Indep R Y P).2 hIndep.symm
  have hProd :=
    hIF.map_prod_eq_prod_map_map hRm.aemeasurable hYm.aemeasurable
  simpa only [Y, R] using hProd
