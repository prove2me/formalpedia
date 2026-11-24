-- Prove2me | solution 1 for Formalism.L2.DIV.idele_conjugation_involutive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:05:31.216401+00:00
-- url     : https://prove2.me/submissions/679e1fb3-60b4-4fce-9e0a-ab3b502c9a6d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_conjugation_involutive
import Theorems.Thm_Formalism_L2_DIV_conjugation_units_val

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
theorem _root_.solution (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (x : (AfE F E)ˣ) : conjId σ (conjId σ x) = x := by
  apply Units.ext
  rw [conjugation_units_val, conjugation_units_val, conjugation_involutive σ hσ]
end Formalism.L2.DIV
