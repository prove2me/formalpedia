-- Prove2me | solution 1 for Formalism.L2.Th1.F.weierstrass_p_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:03:05.656794+00:00
-- url     : https://prove2.me/submissions/742591e4-4b97-4ee9-92ff-20e99507da1f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Theorems.Thm_Formalism_L2_Th1_F_weierstrass_p_of_series
import Theorems.Thm_Formalism_L2_Th1_F_pOfLattice_of
import Theorems.Thm_Formalism_L2_Th1_F_taylorIsWp_of
import Theorems.Thm_Formalism_L2_Th1_F_taylor_deriv
import Theorems.Thm_Formalism_L2_Th1_F_taylor_ring
import Theorems.Thm_Formalism_L2_Th1_F_weierstrass_series_unique


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
theorem _root_.solution : POfLattice :=
  pOfLattice_of (taylorIsWp_of taylor_ring taylor_deriv) weierstrass_series_unique weierstrass_p_of_series
end Formalism.L2.Th1.F
