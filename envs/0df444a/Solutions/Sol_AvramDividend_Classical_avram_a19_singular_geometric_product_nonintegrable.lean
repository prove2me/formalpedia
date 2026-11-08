-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_singular_geometric_product_nonintegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:06:39.630484+00:00
-- url     : https://prove2.me/submissions/e0454c94-a6c8-472e-ae8f-a1f722ba8fee

import Mathlib.Probability.Distributions.Geometric
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_transport_nonintegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- Adding an independent geometric coordinate keeps the singular loss nonintegrable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (p : unitInterval) (hp : p != 0) (hhalf : (p : Real) = 1 / 2)
    (y : Nat → Real)
    (hy : forall k, 0 < y k)
    (hsmall : forall k, y k <= 1 / 16)
    (hpower : forall k, y k <= 1 / ((2 : Real) ^ k) ^ 2) :
    Not (Integrable (fun ωk : Ω × Nat =>
      -(3 + y ωk.2 - 4 * Real.sqrt (y ωk.2) -
        2 / Real.sqrt (y ωk.2)))
      (P.prod (geometricMeasure p))) := by
  have hK : MeasurePreserving (Prod.snd : Ω × Nat → Nat)
      (P.prod (geometricMeasure p)) (geometricMeasure p) :=
    measurePreserving_snd
  exact AvramDividend.Classical.avram_a19_singular_geometric_transport_nonintegrable
    (P.prod (geometricMeasure p)) p hp hhalf
    (Prod.snd : Ω × Nat → Nat) hK y hy hsmall hpower
