-- Prove2me | solution 1 for Formalism.L2.LamCM.finrank_int_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:58.969843+00:00
-- url     : https://prove2.me/submissions/8e595c0f-5884-4e69-9572-b650497ce09b

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
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]
namespace Formalism.L2.LamCM
theorem _root_.solution : Module.finrank (𝓞 K) (𝓞 K1) = Module.finrank K K1 := by
  have h1 := IsLocalization.finrank_eq (R := 𝓞 K) K (N := K1) (𝓞 K)⁰ le_rfl
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K1) (𝓞 K)⁰) K1 :=
    IsIntegralClosure.isLocalization (𝓞 K) K K1 (𝓞 K1)
  haveI : IsLocalizedModule (𝓞 K)⁰ (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K1) K1).toLinearMap :=
    (isLocalizedModule_iff_isLocalization).mpr hloc
  have h2 := IsLocalizedModule.finrank_eq (𝓞 K)⁰ (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K1) K1).toLinearMap le_rfl
  rw [h1, h2]
end Formalism.L2.LamCM
