-- Prove2me | solution 1 for Formalism.L2.DIV.d_res_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:42:45.230723+00:00
-- url     : https://prove2.me/submissions/90869bdc-da35-46d8-8c0a-5869b90d98fc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_d_resMap_surj

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
theorem _root_.solution (hdeg : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (b : 𝓞 E) :
    ∃ n : 𝓞 F, b - algebraMap (𝓞 F) (𝓞 E) n ∈ P.asIdeal := by
  obtain ⟨x, hx⟩ := d_resMap_surj hdeg hv (Ideal.Quotient.mk P.asIdeal b)
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨n, ?_⟩
  rw [← Ideal.Quotient.eq]
  first
  | exact hx.symm
  | simpa [d_resMap] using hx.symm
end Formalism.L2.DIV
