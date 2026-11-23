-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.int_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:58.357997+00:00
-- url     : https://prove2.me/submissions/231af84d-f344-455c-be34-91508cb59e3b

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
theorem _root_.solution {m n : Type} {x y : Matrix m n k0}
    (hx : Integral o x) (hy : Integral o y) : Integral o (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by ext; simp⟩
end Formalism.FourierDecayAlt.P.S3x8
