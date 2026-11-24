-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaBasic_trace_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:02.082315+00:00
-- url     : https://prove2.me/submissions/ae0aa31b-edc2-4881-bee9-119894d14b32

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.K
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [StarRing K] (a : K) :
    Algebra.trace ℚ K (star a) = Algebra.trace ℚ K a := by
  let e : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut K))
    (fun x => ((starRingAut : K ≃+* K).toRingHom.map_rat_algebraMap x))
  exact Algebra.trace_eq_of_algEquiv e a
end Formalism.HermitianLatticesTheory
