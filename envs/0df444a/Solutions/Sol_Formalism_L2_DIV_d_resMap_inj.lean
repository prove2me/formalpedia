-- Prove2me | solution 1 for Formalism.L2.DIV.d_resMap_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:26:40.043015+00:00
-- url     : https://prove2.me/submissions/b984a198-e7b5-4ca0-a6c4-b57032f8887d

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : P.asIdeal.under (𝓞 F) = v.asIdeal) : Function.Injective (d_resMap v P h) := by
  first
  | exact Ideal.quotientMap_injective' (le_of_eq h)
  | (unfold d_resMap
     exact Ideal.quotientMap_injective' (le_of_eq h))
  | (haveI := v.isMaximal
     letI := Ideal.Quotient.field v.asIdeal
     haveI : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial P.isPrime.ne_top
     exact RingHom.injective _)
end Formalism.L2.DIV
