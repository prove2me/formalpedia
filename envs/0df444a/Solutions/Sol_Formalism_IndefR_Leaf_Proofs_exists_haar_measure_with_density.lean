-- Prove2me | solution 1 for Formalism.IndefR.Leaf.Proofs.exists_haar_measure_with_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:38:30.12667+00:00
-- url     : https://prove2.me/submissions/b9c5e3cd-25b3-437e-a803-533533293615

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_MinfUnique
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_MinfUniqueP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Leaf Formalism.IndefR.Leaf.Proofs
open Formalism.IndefR.Leaf MeasureTheory Formalism.BasicNotions
namespace Formalism.IndefR.Leaf.Proofs
theorem _root_.solution (p q : ℕ) (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    ∃ m : Measure (UpqT p q), m.IsHaarMeasure ∧ OmegaDensity m c := by
  obtain ⟨c', hc'0, hc't, hd⟩ :=
    Formalism.BasicNotions.Examples₂.CD.omegaDensity_haar p q (MeasureTheory.Measure.haar : Measure (UpqT p q))
  refine ⟨(c / c') • MeasureTheory.Measure.haar, ?_, ?_⟩
  · exact MeasureTheory.Measure.IsHaarMeasure.smul _ (ENNReal.div_pos_iff.mpr ⟨hc0, hc't⟩).ne'
      (ENNReal.div_lt_top hct hc'0).ne
  · have h := Formalism.BasicNotions.Examples₂.CD.omegaDensity_smul p q hd (c / c') (ENNReal.div_lt_top hct hc'0).ne
    rwa [ENNReal.div_mul_cancel hc'0 hc't] at h
end Formalism.IndefR.Leaf.Proofs
