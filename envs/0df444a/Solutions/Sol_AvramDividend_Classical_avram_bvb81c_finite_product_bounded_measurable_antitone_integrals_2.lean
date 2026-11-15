-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb81c_finite_product_bounded_measurable_antitone_integrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:28:40.021234+00:00
-- url     : https://prove2.me/submissions/0fd1373b-930a-47db-90b6-eaeefdfc8e77

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
/- Finite-measure bounded-kernel integration preserves pointwise antitonicity.
   Joint measurability supplies inner and outer Bochner integrability. -/

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (ν : Measure β) [IsFiniteMeasure ν]
    (f : ℕ → α → β → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hMeas : ∀ n : ℕ, Measurable (Function.uncurry (f n)))
    (hBound : ∀ n a b, ‖f n a b‖ ≤ K)
    (hAntitone : ∀ n m : ℕ, n ≤ m → ∀ a b, f m a b ≤ f n a b) :
    Antitone (fun n : ℕ => ∫ a, ∫ b, f n a b ∂ν ∂μ) := by
  classical
  have hInner (k : ℕ) (a : α) :
      Integrable (f k a) ν := by
    have hm : Measurable (f k a) :=
      (hMeas k).comp (measurable_const.prodMk measurable_id)
    have hSM : AEStronglyMeasurable (f k a) ν :=
      hm.aestronglyMeasurable
    exact Integrable.of_bound hSM K
      (Filter.Eventually.of_forall (fun b => hBound k a b))
  have hOuter (k : ℕ) :
      Integrable (fun a => ∫ b, f k a b ∂ν) μ := by
    have hm : StronglyMeasurable (fun a => ∫ b, f k a b ∂ν) :=
      (hMeas k).stronglyMeasurable.integral_prod_right
    have hSM : AEStronglyMeasurable
        (fun a => ∫ b, f k a b ∂ν) μ :=
      hm.aestronglyMeasurable
    apply Integrable.of_bound hSM (K * ν.real Set.univ)
    filter_upwards [] with a
    exact norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall (fun b => hBound k a b))
  intro n m hnm
  apply integral_mono (hOuter m) (hOuter n)
  intro a
  apply integral_mono (hInner m a) (hInner n a)
  exact hAntitone n m hnm a
