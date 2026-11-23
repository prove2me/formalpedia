-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.range_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:34.973456+00:00
-- url     : https://prove2.me/submissions/feeb7ab4-56b4-42a1-b705-4e768940fef9

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
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution (a : o) (x : k0) (hx : x ∈ (algebraMap o k0).toAddMonoidHom.range) :
    algebraMap o k0 a * x ∈ (algebraMap o k0).toAddMonoidHom.range := by
  obtain ⟨b, rfl⟩ := hx
  exact ⟨a * b, by simp⟩
end Formalism.FourierDecayAlt.P.S3x8
