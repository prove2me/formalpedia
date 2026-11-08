-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_singular_geometric_transport_nonintegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:56:47.815802+00:00
-- url     : https://prove2.me/submissions/bb2c7dac-6c0d-4e29-a1e5-da2178f5350c

import Mathlib.Probability.Distributions.Geometric
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_not_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- The singular geometric counterexample survives measure-preserving sampling. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : unitInterval) (hp : p != 0) (hhalf : (p : Real) = 1 / 2)
    (K : Ω → Nat)
    (hK : MeasurePreserving K P (geometricMeasure p))
    (y : Nat → Real)
    (hy : forall k, 0 < y k)
    (hsmall : forall k, y k <= 1 / 16)
    (hpower : forall k, y k <= 1 / ((2 : Real) ^ k) ^ 2) :
    Not (Integrable (fun ω =>
      -(3 + y (K ω) - 4 * Real.sqrt (y (K ω)) -
        2 / Real.sqrt (y (K ω)))) P) := by
  let g : Nat → Real := fun k =>
    -(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))
  have hgm : AEStronglyMeasurable g (geometricMeasure p) :=
    (measurable_of_countable g).aestronglyMeasurable
  intro hi
  have hc : Integrable (g ∘ K) P := by
    simpa [g, Function.comp_def] using hi
  have hbase : Integrable g (geometricMeasure p) :=
    (hK.integrable_comp hgm).mp hc
  exact (AvramDividend.Classical.avram_a19_singular_geometric_not_integrable
    p hp hhalf y hy hsmall hpower) hbase
