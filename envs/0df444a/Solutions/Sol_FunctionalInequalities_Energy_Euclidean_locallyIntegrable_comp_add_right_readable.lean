-- Prove2me | solution 1 for FunctionalInequalities.Energy.Euclidean.locallyIntegrable_comp_add_right_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:09.69314+00:00
-- url     : https://prove2.me/submissions/0fd97d1d-cfd7-4c49-be5e-8ea3f3f80586

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
omit [SecondCountableTopology V] in
/-- Translates of a locally integrable function are locally integrable for Haar measure. -/
theorem solution {h : V → ℝ} (hh : LocallyIntegrable h m) (v : V) :
    LocallyIntegrable (fun x => h (x + v)) m := by
  refine locallyIntegrable_iff.mpr ?_
  intro K hK
  have hKv : IsCompact ((fun x : V => x + v) '' K) :=
    hK.image (continuous_add_const v)
  have hi : IntegrableOn h ((fun x : V => x + v) '' K) m :=
    hh.integrableOn_isCompact hKv
  have hchange :
      IntegrableOn h ((fun x : V => x + v) '' K) m ↔
        IntegrableOn (h ∘ (fun x : V => x + v)) K m :=
    (measurePreserving_add_right m v).integrableOn_image
      (MeasurableEquiv.addRight v).measurableEmbedding
  have hi' := hchange.mp hi
  simpa [Function.comp_def] using hi'
