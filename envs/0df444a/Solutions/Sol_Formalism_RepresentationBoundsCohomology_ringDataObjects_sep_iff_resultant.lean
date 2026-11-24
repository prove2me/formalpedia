-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.sep_iff_resultant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:32.159984+00:00
-- url     : https://prove2.me/submissions/bc671d2c-adf7-400d-b919-466eb06ef59e

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {K : Type*} [Field K] (f : Polynomial K) (hf : f.Monic) :
    f.resultant f.derivative f.natDegree f.natDegree ≠ 0 ↔ f.Separable := by
  have hd : (Polynomial.derivative f).natDegree ≤ f.natDegree :=
    (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le _ _)
  have h := Polynomial.resultant_add_right_deg f (Polynomial.derivative f) f.natDegree
    (Polynomial.derivative f).natDegree (f.natDegree - (Polynomial.derivative f).natDegree) le_rfl
  rw [Nat.add_sub_cancel' hd, Polynomial.coeff_natDegree, hf.leadingCoeff, one_pow, one_mul] at h
  rw [h, ← isUnit_iff_ne_zero, Polynomial.isUnit_resultant_iff_isCoprime hf]
  exact Iff.rfl
end Formalism.RepresentationBoundsCohomology.ringDataObjects
