-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a322_finite_masked_combined_Gaussian_raw_centered_C2_source_aestrongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:18:59.688236+00:00
-- url     : https://prove2.me/submissions/29a1d2a1-a9ab-4127-93df-36b6672668a8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a167_masked_positive_C2_gaussian_source_residual_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ)
    (hw0 : ContinuousOn w (Ioi (0 : ℝ)))
    (hw1 : ContinuousOn (deriv w) (Ioi (0 : ℝ)))
    (hw2 : ContinuousOn (iteratedDeriv 2 w) (Ioi (0 : ℝ)))
    (m : ℕ) (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (hA : ∀ i, MeasurableSet {ω | A i ω})
    (Y R : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hR : ∀ i, Measurable (R i))
    (hPos : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      A i ω → 0 < Y i ω ∧ 0 < Y i ω + R i ω)
    (d c σ : ℝ) (E0 E1 : ℕ → ℝ) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range m, if A i ω then
        E1 i * (w (Y i ω+R i ω)-w (Y i ω)) -
        E0 i * (deriv w (Y i ω)*R i ω +
          iteratedDeriv 2 w (Y i ω)/2*(R i ω-d*c)^2)
        else 0) P := by
  let S : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m, if A i ω then
      E1 i*(w (Y i ω+R i ω)-w (Y i ω)) -
      E0 i*(deriv w (Y i ω)*R i ω +
        iteratedDeriv 2 w (Y i ω)/2*(R i ω-d*c)^2)
      else 0
  have hm := avram_ga_a167_masked_positive_C2_gaussian_source_residual_measurable
    P w hw0 hw1 hw2 m A hA Y R hY hR hPos d c σ E0 E1
  have heq (ω : Ω) : S ω =
      (∑ i ∈ Finset.range m, if A i ω then
        E1 i*(w (Y i ω+R i ω)-w (Y i ω)) -
        (E0 i*(deriv w (Y i ω)*(R i ω-d*c) +
          iteratedDeriv 2 w (Y i ω)/2*
            ((R i ω-d*c)^2-d*σ^2)) +
          d*E0 i*(σ^2/2*iteratedDeriv 2 w (Y i ω)+
            c*deriv w (Y i ω)))
        else 0) := by
    dsimp [S]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> try rfl
    ring
  exact hm.congr (Filter.Eventually.of_forall (fun ω => (heq ω).symm))
