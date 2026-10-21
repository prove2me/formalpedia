-- Prove2me | solution 1 for AvramDividend.Classical.chat04_levy_three_consecutive_increment_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:47:03.320659+00:00
-- url     : https://prove2.me/submissions/a69dc14d-35f0-41f3-8a73-93a55b8f9ea5

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_random_state_increment_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Three consecutive Lévy state/increment components have their full joint
law equal to the nested product of the three marginals. Independence of the
second increment is from F_t, which already contains the first two states.
This is the finite-grid stochastic input for path-dependent killing.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) :
    Measure.map
      (fun ω => ((X.X s ω, X.X t ω - X.X s ω),
        X.X u ω - X.X t ω)) P =
      ((Measure.map (X.X s) P).prod
        (Measure.map (X.X (t - s)) P)).prod
          (Measure.map (X.X (u - t)) P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let f : Ω → ℝ × ℝ :=
    fun ω => (X.X s ω, X.X t ω - X.X s ω)
  let g : Ω → ℝ := fun ω => X.X u ω - X.X t ω
  have hXs_t : Measurable[𝓕 t] (X.X s) :=
    (X.adapted s).mono (𝓕.mono hst) le_rfl
  have hXt_t : Measurable[𝓕 t] (X.X t) :=
    X.adapted t
  have hf_t : Measurable[𝓕 t] f := by
    dsimp [f]
    exact hXs_t.prodMk (hXt_t.sub hXs_t)
  have hf : Measurable f :=
    hf_t.mono (𝓕.le t) le_rfl
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hXu : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hg : Measurable g := by
    dsimp [g]
    exact hXu.sub hXt
  have hSub : MeasurableSpace.comap f inferInstance ≤ 𝓕 t :=
    hf_t.comap_le
  have hIndep :
      Indep (MeasurableSpace.comap f inferInstance)
        (MeasurableSpace.comap g inferInstance) P := by
    have h0 : Indep (MeasurableSpace.comap g inferInstance) (𝓕 t) P := by
      simpa only [g] using X.indepIncrements t u htu
    exact (indep_of_indep_of_le_right h0 hSub).symm
  have hIF : IndepFun f g P :=
    (IndepFun_iff_Indep f g P).2 hIndep
  have hProd :
      Measure.map (fun ω => (f ω, g ω)) P =
        (Measure.map f P).prod (Measure.map g P) :=
    hIF.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hLaw : Measure.map g P =
        Measure.map (X.X (u - t)) P := by
    simpa only [g] using (X.stationaryIncrements t u htu).map_eq
  have hEarlier :
      Measure.map f P =
        (Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P) := by
    simpa only [f] using
      AvramDividend.Classical.chat04_levy_random_state_increment_product_law
        X s t hst
  calc
    Measure.map
        (fun ω => ((X.X s ω, X.X t ω - X.X s ω),
          X.X u ω - X.X t ω)) P =
      Measure.map (fun ω => (f ω, g ω)) P := by rfl
    _ = (Measure.map f P).prod (Measure.map g P) := hProd
    _ = ((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)).prod
          (Measure.map (X.X (u - t)) P) := by
        rw [hEarlier, hLaw]
