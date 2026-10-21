-- Prove2me | solution 1 for AvramDividend.Classical.chat04_scale_random_state_tonelli_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:33:26.572638+00:00
-- url     : https://prove2.me/submissions/6f6d8516-b5f9-41da-97b2-1e659e88c41f

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Random-state Markov semigroup input for the q-scale function. Derive the
product joint law of (X_s, X_t-X_s) from the official Lévy axioms, then
use Tonelli. No integrability or killed-scale harmonicity is assumed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (W (x + X.X t ω)) ∂P) =
      ∫⁻ u, ∫⁻ v, ENNReal.ofReal (W (x + u + v))
          ∂(Measure.map (X.X (t - s)) P)
          ∂(Measure.map (X.X s) P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let g : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  let f : ℝ × ℝ → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (W (x + z.1 + z.2))
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hg : Measurable g := by
    dsimp [g]
    exact hXt.sub hXs
  have hWmeas : Measurable W :=
    AvramDividend.Classical.chat03_scale_function_borel_measurable X q W hW
  have hf : Measurable f := by
    dsimp [f]
    exact ENNReal.measurable_ofReal.comp
      (hWmeas.comp ((measurable_const.add measurable_fst).add measurable_snd))
  have hpair : Measurable (fun ω => (X.X s ω, g ω)) :=
    hXs.prodMk hg
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
  have hProdStationary :
      Measure.map (fun ω => (X.X s ω, g ω)) P =
        (Measure.map (X.X s) P).prod (Measure.map (X.X (t - s)) P) := by
    rw [hProd, hLaw]
  calc
    (∫⁻ ω, ENNReal.ofReal (W (x + X.X t ω)) ∂P) =
        ∫⁻ ω, f (X.X s ω, g ω) ∂P := by
          apply lintegral_congr
          intro ω
          dsimp [f, g]
          congr 1
          congr 1
          ring
    _ = ∫⁻ z, f z ∂Measure.map (fun ω => (X.X s ω, g ω)) P := by
          rw [lintegral_map hf hpair]
    _ = ∫⁻ z, f z ∂
        ((Measure.map (X.X s) P).prod (Measure.map (X.X (t - s)) P)) := by
          rw [hProdStationary]
    _ = ∫⁻ u, ∫⁻ v, ENNReal.ofReal (W (x + u + v))
          ∂(Measure.map (X.X (t - s)) P)
          ∂(Measure.map (X.X s) P) := by
          simpa only [f] using
            (lintegral_prod f hf.aemeasurable)
