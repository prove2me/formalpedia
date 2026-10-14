-- Prove2me | solution 1 for DistCov.Indep.dcov_integrable
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T21:31:06.35638+00:00
-- url     : https://prove2.me/submissions/859166a6-8446-41a9-9411-dd9baafae343

import Theorems.Thm_DistCov_Indep_lemma_2_1

set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure

namespace DistCovIntegrability
lemma product_map_preserving {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (θ : Measure A) [SFinite θ] (f : A → B) (hf : Measurable f) :
    MeasurePreserving (Prod.map f f) (θ.prod θ) ((θ.map f).prod (θ.map f)) := by
  exact ⟨hf.prodMap hf, (Measure.map_prod_map θ θ hf hf).symm⟩
end DistCovIntegrability

open DistCov.Indep

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (θ : Measure (X × Y)) [IsProbabilityMeasure θ]
    (hμ : FiniteFirstMoment (θ.map Prod.fst)) (hν : FiniteFirstMoment (θ.map Prod.snd)) :
    Integrable (fun pq : (X × Y) × (X × Y) =>
      dcent (θ.map Prod.fst) pq.1.1 pq.2.1 * dcent (θ.map Prod.snd) pq.1.2 pq.2.2) (θ.prod θ) := by
  letI : IsProbabilityMeasure (θ.map Prod.fst) := isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (θ.map Prod.snd) := isProbabilityMeasure_map measurable_snd.aemeasurable
  have hx := (lemma_2_1 (θ.map Prod.fst) hμ).comp_measurePreserving
    (DistCovIntegrability.product_map_preserving θ Prod.fst measurable_fst)
  have hy := (lemma_2_1 (θ.map Prod.snd) hν).comp_measurePreserving
    (DistCovIntegrability.product_map_preserving θ Prod.snd measurable_snd)
  exact hx.integrable_mul hy
#print axioms solution
