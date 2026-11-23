-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.res_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:32.060657+00:00
-- url     : https://prove2.me/submissions/0642966b-102b-4c1f-ae32-1eec9330c0f7

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]
variable [IsDomain o] [IsDiscreteValuationRing o]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {ϖ : o} (hϖ : Irreducible ϖ) : IsLocalRing.residue o ϖ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq]
  exact Ideal.mem_span_singleton_self ϖ
end Formalism.FourierDecayAlt.P.S3x8
