-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.diag_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:39.791026+00:00
-- url     : https://prove2.me/submissions/f441cd44-3925-4013-a493-8cd4d4e20fbe

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_eval_single_point_id
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {O : Type} [CommRing O] [StarRing O]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
theorem _root_.solution (B : FB S d O) (w0 : O) (p : Fin 2) (q : Fin d) :
    MvPowerSeries.constantCoeff ((![pt S (n := 1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)] : Fin 2 → Pt S 1 d) p q) = 0 := by
  fin_cases p
  · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · have h1 : comp1 (B.A.act w0) (pt S (n := 1) d 0) q = B.A.act w0 q := eval_single_point_id _
    simpa [h1] using B.A.const w0 q
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
