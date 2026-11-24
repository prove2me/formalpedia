-- Prove2me | solution 1 for Formalism.L2.DIV.d_resMap_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:42.546773+00:00
-- url     : https://prove2.me/submissions/bdee6e0f-a3b1-408d-8f15-2ede41ce2a70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_d_resMap_inj
import Theorems.Thm_Formalism_L2_DIV_d_finite_quot
import Theorems.Thm_Formalism_L2_DIV_d_absNorm_eq

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
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    Function.Surjective (d_resMap v P (d_under hv)) := by
  have hi := d_resMap_inj v P (d_under hv)
  haveI := d_finite_quot P
  have hc : Nat.card (𝓞 E ⧸ P.asIdeal) ≤ Nat.card (𝓞 F ⧸ v.asIdeal) := by
    have := d_absNorm_eq hdeg hv
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply] at this
    exact this.le
  exact (hi.bijective_of_nat_card_le hc).2
end Formalism.L2.DIV
