-- Prove2me | solution 1 for Formalism.L2.LamCM.count_coeIdeal_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:02.477657+00:00
-- url     : https://prove2.me/submissions/629e0eba-ef82-4b49-bd7c-67e0ba3d8ec8

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
section
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
section counts
variable {F : Type} [Field F] [NumberField F]
private lemma count_coeIdeal_eq_zero_of_not_le (v : HeightOneSpectrum (𝓞 F)) {J : Ideal (𝓞 F)} (h : ¬ J ≤ v.asIdeal) :
    FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
  have hJ : J ≠ 0 := fun h0 => h (h0 ▸ bot_le)
  rw [FractionalIdeal.count_coe F v hJ]
  by_contra hne
  have hne' : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 := by exact_mod_cast hne
  exact h (Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd hJ v.irreducible).mp hne'))
end counts
section bc
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]
end bc
end Formalism.L2.LamCM
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.LamCM
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {J : Ideal (𝓞 F)} (h : ¬ J ≤ v.asIdeal) :
    FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) = 0 := count_coeIdeal_eq_zero_of_not_le v h
end Formalism.L2.LamCM
