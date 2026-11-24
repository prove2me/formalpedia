-- Prove2me | solution 1 for Formalism.L2.LamCM.not_le_of_count_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:31.621769+00:00
-- url     : https://prove2.me/submissions/5f3d3bcc-4d4f-47e3-b0c9-4cb478383626

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.LamCM
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {J : Ideal (𝓞 F)} (hJ : J ≠ ⊥)
    (h : FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) = 0) : ¬ J ≤ v.asIdeal := by
  intro hle
  have hne : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 :=
    (Associates.count_ne_zero_iff_dvd hJ v.irreducible).mpr (Ideal.dvd_iff_le.mpr hle)
  rw [FractionalIdeal.count_coe F v hJ] at h
  exact hne (by exact_mod_cast h)
end Formalism.L2.LamCM
