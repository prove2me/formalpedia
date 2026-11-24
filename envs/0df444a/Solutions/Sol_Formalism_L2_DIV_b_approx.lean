-- Prove2me | solution 1 for Formalism.L2.DIV.b_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:05:31.563073+00:00
-- url     : https://prove2.me/submissions/f4a35046-83c2-4df7-8d5a-201e2ab9ab40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_toRInt_val
import Theorems.Thm_Formalism_L2_DIV_b_toRInt_alg
import Theorems.Thm_Formalism_UG_P_csGlob_approx
import Theorems.Thm_Formalism_UG_P_csGlob_intAdApprox


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
theorem _root_.solution (D : 𝓞 F) (hD : D ≠ 0) (s : RInt F E) :
    ∃ (b : 𝓞 E) (t : RInt F E), s = toRInt F E b + toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) * t := by
  obtain ⟨b, t, ht, h⟩ := csGlob_approx csGlob_intAdApprox D hD (s : AfE F E) s.2
  refine ⟨b, ⟨t, ht⟩, Subtype.ext ?_⟩
  rw [h]
  show _ = ((toRInt F E b : RInt F E) : AfE F E) +
    ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) : RInt F E) : AfE F E) * t
  rw [b_toRInt_alg, b_toRInt_val]
  rfl
end Formalism.L2.DIV
