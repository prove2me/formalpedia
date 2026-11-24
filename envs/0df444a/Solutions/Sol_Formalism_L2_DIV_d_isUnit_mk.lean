-- Prove2me | solution 1 for Formalism.L2.DIV.d_isUnit_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:25:16.73517+00:00
-- url     : https://prove2.me/submissions/b719b8af-05e6-4b22-bdc6-3b50beee679e

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
set_option quotPrecheck false in
local notation "uIn" => Units.map (RInt F E).subtype.toMonoidHom
namespace Formalism.L2.DIV
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) {b : 𝓞 E} (hb : b ∉ P.asIdeal) :
    IsUnit (Ideal.Quotient.mk P.asIdeal b) := by
  first
  | (obtain ⟨y, i, hi, hyi⟩ := P.isMaximal.exists_inv hb
     refine isUnit_of_mul_eq_one _ (Ideal.Quotient.mk P.asIdeal y) ?_
     rw [← map_mul, ← map_one (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq]
     have e : b * y - 1 = -i := by rw [← hyi]; ring
     rw [e]
     exact P.asIdeal.neg_mem hi)
  | (haveI := P.isMaximal
     letI := Ideal.Quotient.field P.asIdeal
     exact isUnit_iff_ne_zero.mpr (fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h)))
end Formalism.L2.DIV
