-- Prove2me | solution 1 for AvramDividend.Classical.chat04_levy_random_state_increment_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:26:34.369369+00:00
-- url     : https://prove2.me/submissions/59e3e814-6f53-4487-82c8-96a1195937a0

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
Exact joint law of the observed Lévy reserve and the independent future
increment. The product law is the foundational random-state Markov coupling.
No q-scale assumption or martingale is used.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Measure.map
        (fun ω => (X.X s ω, X.X t ω - X.X s ω)) P =
      (Measure.map (X.X s) P).prod (Measure.map (X.X (t - s)) P) := by
  let g : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  letI : IsProbabilityMeasure P := X.isProbability
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hg : Measurable g := by
    dsimp [g]
    exact hXt.sub hXs
  have hSub :
      MeasurableSpace.comap (X.X s) inferInstance ≤ 𝓕 s :=
    (X.adapted s).comap_le
  have hIndep :
      Indep (MeasurableSpace.comap (X.X s) inferInstance)
        (MeasurableSpace.comap g inferInstance) P := by
    have h0 : Indep (MeasurableSpace.comap g inferInstance) (𝓕 s) P := by
      simpa only [g] using X.indepIncrements s t hst
    exact (indep_of_indep_of_le_right h0 hSub).symm
  have hIF : IndepFun (X.X s) g P :=
    (IndepFun_iff_Indep (X.X s) g P).2 hIndep
  have hProd :
      Measure.map (fun ω => (X.X s ω, g ω)) P =
        (Measure.map (X.X s) P).prod (Measure.map g P) :=
    hIF.map_prod_eq_prod_map_map hXs.aemeasurable hg.aemeasurable
  have hLaw : Measure.map g P = Measure.map (X.X (t - s)) P := by
    simpa only [g] using (X.stationaryIncrements s t hst).map_eq
  simpa only [g, hLaw] using hProd
