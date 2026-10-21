-- Prove2me | solution 1 for AvramDividend.Classical.chat04_three_grid_survival_scale_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:17:37.153554+00:00
-- url     : https://prove2.me/submissions/77ffe383-3f6f-44d2-a957-2c5033c62ea3

import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_three_step_grid_tonelli_markov_law
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Three-point lower-barrier survival payoff factorises into independent
Lévy increment laws. This is the genuine discrete killed-transition
component; no no-creeping claim or continuous-time martingale is assumed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (x : ℝ) :
    (∫⁻ ω,
       if 0 ≤ x + X.X s ω ∧
          0 ≤ x + X.X s ω + (X.X t ω - X.X s ω) ∧
          0 ≤ x + X.X s ω + (X.X t ω - X.X s ω) +
            (X.X u ω - X.X t ω)
       then ENNReal.ofReal
         (W (x + X.X s ω + (X.X t ω - X.X s ω) +
            (X.X u ω - X.X t ω)))
       else 0 ∂P) =
    ∫⁻ a, ∫⁻ b, ∫⁻ c,
       if 0 ≤ x + a ∧ 0 ≤ x + a + b ∧
          0 ≤ x + a + b + c
       then ENNReal.ofReal (W (x + a + b + c))
       else 0
       ∂(Measure.map (X.X (u - t)) P)
       ∂(Measure.map (X.X (t - s)) P)
       ∂(Measure.map (X.X s) P) := by
  let f : (ℝ × ℝ) × ℝ → ℝ≥0∞ :=
    fun z =>
      if 0 ≤ x + z.1.1 ∧ 0 ≤ x + z.1.1 + z.1.2 ∧
         0 ≤ x + z.1.1 + z.1.2 + z.2
      then ENNReal.ofReal (W (x + z.1.1 + z.1.2 + z.2))
      else 0
  have hWm : Measurable W :=
    AvramDividend.Classical.chat03_scale_function_borel_measurable X q W hW
  have hA : MeasurableSet
      {z : (ℝ × ℝ) × ℝ | 0 ≤ x + z.1.1} := by
    change MeasurableSet
      ((fun z : (ℝ × ℝ) × ℝ => x + z.1.1) ⁻¹' Set.Ici (0 : ℝ))
    exact isClosed_Ici.measurableSet.preimage (by fun_prop)
  have hB : MeasurableSet
      {z : (ℝ × ℝ) × ℝ | 0 ≤ x + z.1.1 + z.1.2} := by
    change MeasurableSet
      ((fun z : (ℝ × ℝ) × ℝ => x + z.1.1 + z.1.2) ⁻¹'
        Set.Ici (0 : ℝ))
    exact isClosed_Ici.measurableSet.preimage (by fun_prop)
  have hC : MeasurableSet
      {z : (ℝ × ℝ) × ℝ | 0 ≤ x + z.1.1 + z.1.2 + z.2} := by
    change MeasurableSet
      ((fun z : (ℝ × ℝ) × ℝ => x + z.1.1 + z.1.2 + z.2) ⁻¹'
        Set.Ici (0 : ℝ))
    exact isClosed_Ici.measurableSet.preimage (by fun_prop)
  have hSurvival : MeasurableSet
      {z : (ℝ × ℝ) × ℝ |
        0 ≤ x + z.1.1 ∧ 0 ≤ x + z.1.1 + z.1.2 ∧
        0 ≤ x + z.1.1 + z.1.2 + z.2} := by
    exact hA.inter (hB.inter hC)
  have hSum : Measurable
      (fun z : (ℝ × ℝ) × ℝ => x + z.1.1 + z.1.2 + z.2) := by
    fun_prop
  have hPayoff :
      Measurable
        (fun z : (ℝ × ℝ) × ℝ =>
          ENNReal.ofReal (W (x + z.1.1 + z.1.2 + z.2))) :=
    ENNReal.measurable_ofReal.comp (hWm.comp hSum)
  have hfm : Measurable f := by
    dsimp [f]
    exact Measurable.ite hSurvival hPayoff measurable_const
  simpa only [f] using
    AvramDividend.Classical.chat04_three_step_grid_tonelli_markov_law
      X s t u hst htu f hfm
