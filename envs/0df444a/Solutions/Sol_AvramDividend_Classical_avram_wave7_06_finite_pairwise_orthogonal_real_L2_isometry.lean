-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_finite_pairwise_orthogonal_real_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:43:13.367216+00:00
-- url     : https://prove2.me/submissions/d18b1124-60f4-4e82-b3bd-3fa8f6ba8277

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Pairwise zero cross expectations yield an exact finite real L² energy
identity; all pair products are integrable to justify both finite sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (n : ℕ) (A : ℕ → Ω → ℝ)
    (hProduct : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => A i ω * A j ω) P)
    (hOrth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i ≠ j → (∫ ω, A i ω * A j ω ∂P) = 0) :
    (∫ ω, (∑ i ∈ Finset.range n, A i ω)^2 ∂P) =
      ∑ i ∈ Finset.range n, ∫ ω, (A i ω)^2 ∂P := by
  let S : Finset ℕ := Finset.range n
  have hOuter : ∀ i ∈ S,
      Integrable (fun ω => ∑ j ∈ S, A i ω * A j ω) P := by
    intro i hi
    apply integrable_finset_sum S
    intro j hj
    exact hProduct i hi j hj
  change (∫ ω, (∑ i ∈ S, A i ω)^2 ∂P) =
    ∑ i ∈ S, ∫ ω, (A i ω)^2 ∂P
  calc
    (∫ ω, (∑ i ∈ S, A i ω)^2 ∂P) =
        ∫ ω, ∑ i ∈ S, ∑ j ∈ S, A i ω * A j ω ∂P := by
      congr 1
      funext ω
      simpa only [pow_two] using
        (Finset.sum_mul_sum S S (fun i => A i ω) (fun j => A j ω))
    _ = ∑ i ∈ S, ∑ j ∈ S, ∫ ω, A i ω * A j ω ∂P := by
      rw [integral_finset_sum S hOuter]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finset_sum S (fun j hj => hProduct i hi j hj)
    _ = ∑ i ∈ S, ∫ ω, (A i ω)^2 ∂P := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j ∈ S, ∫ ω, A i ω * A j ω ∂P) =
            ∫ ω, A i ω * A i ω ∂P := by
          exact Finset.sum_eq_single_of_mem
            (s := S) (a := i)
            (f := fun j => ∫ ω, A i ω * A j ω ∂P) hi
            (by
              intro j hj hji
              exact hOrth i hi j hj (Ne.symm hji))
        _ = ∫ ω, (A i ω)^2 ∂P := by
          congr 1
          funext ω
          ring
