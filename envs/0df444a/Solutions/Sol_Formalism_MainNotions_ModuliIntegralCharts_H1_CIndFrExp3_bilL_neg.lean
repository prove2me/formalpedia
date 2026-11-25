-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.bilL_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:11:26.601799+00:00
-- url     : https://prove2.me/submissions/6d61a424-d4f6-4fb5-944f-e51bedd7d033

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BalOf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IsUnitCoeffZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
variable {S : Type} [CommRing S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
theorem _root_.solution [Algebra ℚ S] (G : FGLaw S d) (c : Fin d → Fin d → S) : bilL G (-c) = -bilL G c := by
  simp only [bilL, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
