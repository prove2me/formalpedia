-- Prove2me | solution 1 for AvramDividend.Classical.chat04_levy_four_consecutive_increment_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:23:22.842245+00:00
-- url     : https://prove2.me/submissions/a3698f83-5baf-4496-8e8f-ff4f5fe14b75

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_three_consecutive_increment_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Four consecutive Lévy state/increment components factor into a nested
product measure. The final increment is independent of the entire past
filtration at u, including all three earlier components.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    Measure.map
      (fun ω => (((X.X s ω, X.X t ω - X.X s ω),
         X.X u ω - X.X t ω), X.X v ω - X.X u ω)) P =
      (((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)).prod
          (Measure.map (X.X (u - t)) P)).prod
          (Measure.map (X.X (v - u)) P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let f : Ω → ((ℝ × ℝ) × ℝ) :=
    fun ω => ((X.X s ω, X.X t ω - X.X s ω),
      X.X u ω - X.X t ω)
  let g : Ω → ℝ := fun ω => X.X v ω - X.X u ω
  have hXs_u : Measurable[𝓕 u] (X.X s) :=
    (X.adapted s).mono (𝓕.mono (hst.trans htu)) le_rfl
  have hXt_u : Measurable[𝓕 u] (X.X t) :=
    (X.adapted t).mono (𝓕.mono htu) le_rfl
  have hXu_u : Measurable[𝓕 u] (X.X u) := X.adapted u
  have hf_u : Measurable[𝓕 u] f := by
    dsimp [f]
    exact (hXs_u.prodMk (hXt_u.sub hXs_u)).prodMk
      (hXu_u.sub hXt_u)
  have hf : Measurable f :=
    hf_u.mono (𝓕.le u) le_rfl
  have hXu : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hXv : Measurable (X.X v) :=
    (X.adapted v).mono (𝓕.le v) le_rfl
  have hg : Measurable g := by
    dsimp [g]
    exact hXv.sub hXu
  have hSub : MeasurableSpace.comap f inferInstance ≤ 𝓕 u :=
    hf_u.comap_le
  have hIndep :
      Indep (MeasurableSpace.comap f inferInstance)
        (MeasurableSpace.comap g inferInstance) P := by
    have h0 : Indep (MeasurableSpace.comap g inferInstance) (𝓕 u) P := by
      simpa only [g] using X.indepIncrements u v huv
    exact (indep_of_indep_of_le_right h0 hSub).symm
  have hIF : IndepFun f g P :=
    (IndepFun_iff_Indep f g P).2 hIndep
  have hProd :
      Measure.map (fun ω => (f ω, g ω)) P =
        (Measure.map f P).prod (Measure.map g P) :=
    hIF.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hLaw : Measure.map g P =
        Measure.map (X.X (v - u)) P := by
    simpa only [g] using (X.stationaryIncrements u v huv).map_eq
  have hEarlier :
      Measure.map f P =
        ((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)).prod
          (Measure.map (X.X (u - t)) P) := by
    simpa only [f] using
      AvramDividend.Classical.chat04_levy_three_consecutive_increment_product_law
        X s t u hst htu
  calc
    Measure.map
        (fun ω => (((X.X s ω, X.X t ω - X.X s ω),
          X.X u ω - X.X t ω), X.X v ω - X.X u ω)) P =
      Measure.map (fun ω => (f ω, g ω)) P := by rfl
    _ = (Measure.map f P).prod (Measure.map g P) := hProd
    _ = (((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)).prod
          (Measure.map (X.X (u - t)) P)).prod
          (Measure.map (X.X (v - u)) P) := by
        rw [hEarlier, hLaw]
