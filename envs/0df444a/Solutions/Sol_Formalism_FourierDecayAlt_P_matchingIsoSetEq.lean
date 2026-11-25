-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.matchingIsoSetEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:44:35.409704+00:00
-- url     : https://prove2.me/submissions/8a93e9d4-81c4-438f-b3de-63b5daf0d9de

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.IsoZZIsIso := by
  intro K _ R n n' Z Z' lam' h
  ext φ
  simp only [isoZZ, isoSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v => ?_⟩
    obtain ⟨v', hv'⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk v))
    rw [← hv', h]; exact h2 v v' hv'.symm
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v v' hv => ?_⟩
    rw [← h2 v, hv, h]
end Formalism.FourierDecayAlt.P
