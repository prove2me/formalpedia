-- Prove2me | solution 1 for Formalism.L2.DIV.include_right_injective_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:29:21.387109+00:00
-- url     : https://prove2.me/submissions/31abeb92-6091-4ea8-9b1e-76c8ec07e3eb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] :
    Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective
end Formalism.L2.DIV
