-- Prove2me | solution 1 for Formalism.L2.DIV.d_absNorm_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:25:16.045257+00:00
-- url     : https://prove2.me/submissions/1aad32bc-8b1d-4642-ae44-98cc093e49b4

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
theorem _root_.solution (hdeg : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal) = Ideal.absNorm v.asIdeal ^ 2 := by
  rw [← Ideal.absNorm_relNorm (R := 𝓞 F), Ideal.relNorm_algebraMap, map_pow,
    ← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, hdeg]
end Formalism.L2.DIV
