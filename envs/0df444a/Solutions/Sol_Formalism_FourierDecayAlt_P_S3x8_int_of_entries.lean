-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.int_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:48.402315+00:00
-- url     : https://prove2.me/submissions/2954dd53-f2df-4e7f-9e81-e5f6b07457a6

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
theorem _root_.solution {m n : Type} {x : Matrix m n k0}
    (h : ∀ a b, x a b ∈ (algebraMap o k0).toAddMonoidHom.range) : Integral o x := by
  choose y hy using h
  exact ⟨Matrix.of y, by ext a b; exact hy a b⟩
end Formalism.FourierDecayAlt.P.S3x8
