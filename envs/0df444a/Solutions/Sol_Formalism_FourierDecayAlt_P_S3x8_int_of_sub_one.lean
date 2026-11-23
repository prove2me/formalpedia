-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.int_of_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:38.278564+00:00
-- url     : https://prove2.me/submissions/515c88fc-609a-4994-83e8-15bc9c0bd572

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_of_entries

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
theorem _root_.solution {m : Type} [DecidableEq m] {x : Matrix m m k0}
    (h : ∀ a b, (x - 1) a b ∈ (algebraMap o k0).toAddMonoidHom.range) : Integral o x := by
  have := int_add (int_of_entries h) (int_one (o := o) (k0 := k0) (m := m))
  simpa using this
end Formalism.FourierDecayAlt.P.S3x8
