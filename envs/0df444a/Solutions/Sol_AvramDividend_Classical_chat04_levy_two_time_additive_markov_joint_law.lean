-- Prove2me | solution 1 for AvramDividend.Classical.chat04_levy_two_time_additive_markov_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:39:18.429849+00:00
-- url     : https://prove2.me/submissions/1d395748-71c1-47f7-947b-4b44417885b0

import Mathlib.MeasureTheory.Measure.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_random_state_increment_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The two-time Markov joint law is a deterministic additive image of the
independent current-state/future-increment product law. No q-scale and no
martingale assumption is required.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Measure.map (fun ω => (X.X s ω, X.X t ω)) P =
      Measure.map
        (fun z : ℝ × ℝ => (z.1, z.1 + z.2))
        ((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)) := by
  let m : ℝ × ℝ → ℝ × ℝ :=
    fun z => (z.1, z.1 + z.2)
  let g : Ω → ℝ × ℝ :=
    fun ω => (X.X s ω, X.X t ω - X.X s ω)
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hg : Measurable g := by
    dsimp [g]
    exact hXs.prodMk (hXt.sub hXs)
  have hm : Measurable m := by
    dsimp [m]
    exact measurable_fst.prodMk (measurable_fst.add measurable_snd)
  have hproduct :
      Measure.map g P =
        (Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P) := by
    simpa only [g] using
      AvramDividend.Classical.chat04_levy_random_state_increment_product_law
        X s t hst
  calc
    Measure.map (fun ω => (X.X s ω, X.X t ω)) P =
      Measure.map (m ∘ g) P := by
        congr 1
        funext ω
        dsimp [m, g, Function.comp_def]
        congr 1
        ring
    _ = Measure.map m (Measure.map g P) := by
      exact (Measure.map_map hm hg).symm
    _ = Measure.map m ((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)) := by
      rw [hproduct]
    _ = Measure.map
        (fun z : ℝ × ℝ => (z.1, z.1 + z.2))
        ((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)) := by
      rfl
