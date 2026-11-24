-- Prove2me | solution 1 for Formalism.L2.Th1.F.pOfLattice_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:11.254745+00:00
-- url     : https://prove2.me/submissions/dad9c0df-e26e-43aa-a6bc-7440804b9199

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW wpNum wpDen)
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open POf
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : TaylorIsWp) (hu : IsWpUnique) (hp : POfIsWp) : POfLattice :=
  fun L => hu ℂ L.g₂ L.g₃ _ _ (h L) (hp ℂ L.g₂ L.g₃)
end Formalism.L2.Th1.F
