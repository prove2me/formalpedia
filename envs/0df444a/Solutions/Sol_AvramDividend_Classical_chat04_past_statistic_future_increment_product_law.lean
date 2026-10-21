-- Prove2me | solution 1 for AvramDividend.Classical.chat04_past_statistic_future_increment_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:30:28.870264+00:00
-- url     : https://prove2.me/submissions/2b1b6a28-5765-4a78-b164-86062e47577d

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Full-filtration Lévy independence is not restricted to the observed value
X_s: every history-measurable statistic of any measurable target type E is
independent of the future increment. This supplies the induction step for
arbitrary finite histories of monitoring times and path-dependent killing.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    Measure.map (fun ω => (H ω, X.X t ω - X.X s ω)) P =
      (Measure.map H P).prod
        (Measure.map (X.X (t - s)) P) := by
  let g : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  letI : IsProbabilityMeasure P := X.isProbability
  have hHm : Measurable H :=
    hH.mono (𝓕.le s) le_rfl
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hg : Measurable g := by
    dsimp [g]
    exact hXt.sub hXs
  have hSub :
      MeasurableSpace.comap H inferInstance ≤ 𝓕 s :=
    hH.comap_le
  have hIndep :
      Indep (MeasurableSpace.comap H inferInstance)
        (MeasurableSpace.comap g inferInstance) P := by
    have h0 : Indep (MeasurableSpace.comap g inferInstance) (𝓕 s) P := by
      simpa only [g] using X.indepIncrements s t hst
    exact (indep_of_indep_of_le_right h0 hSub).symm
  have hIF : IndepFun H g P :=
    (IndepFun_iff_Indep H g P).2 hIndep
  have hProd :
      Measure.map (fun ω => (H ω, g ω)) P =
        (Measure.map H P).prod (Measure.map g P) :=
    hIF.map_prod_eq_prod_map_map hHm.aemeasurable hg.aemeasurable
  have hLaw : Measure.map g P =
      Measure.map (X.X (t - s)) P := by
    simpa only [g] using (X.stationaryIncrements s t hst).map_eq
  simpa only [g, hLaw] using hProd
