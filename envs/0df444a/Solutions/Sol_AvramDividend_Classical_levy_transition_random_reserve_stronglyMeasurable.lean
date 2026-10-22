-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_random_reserve_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:28:49.068954+00:00
-- url     : https://prove2.me/submissions/c2f0e00c-eec9-4189-aba0-90bca19bad18


import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_preserves_lipschitz_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ u : ℝ, Integrable
      (fun η => f (u + X.X t η)) P)
    (Z : Ω → ℝ) (hZ : Measurable Z) :
    StronglyMeasurable (fun ω =>
      ∫ η, f (Z ω + X.X t η) ∂P) := by
  let T (u : ℝ) : ℝ := ∫ η, f (u + X.X t η) ∂P
  let K : ℝ≥0 := ⟨L, hL⟩
  have hLipT : LipschitzWith K T := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hb :=
      levy_transition_preserves_lipschitz_bound
        X t f L hL hLip hInt u v
    simp only [Real.dist_eq]
    change |T u - T v| ≤ L * |u - v|
    exact hb
  have hTM : StronglyMeasurable (T ∘ Z) :=
    (hLipT.continuous.measurable.comp hZ).stronglyMeasurable
  simpa only [T, Function.comp_def] using hTM

