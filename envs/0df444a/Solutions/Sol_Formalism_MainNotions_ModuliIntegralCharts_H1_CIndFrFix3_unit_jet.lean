-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.unit_jet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:59.552738+00:00
-- url     : https://prove2.me/submissions/8ecf1132-c25d-4a26-a49a-19db6728042c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_jet_sL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_const_diagL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_eval_expSeries_neg_bilinear
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_exp_pow_inv
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_psJet_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_one
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
theorem _root_.solution (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) (m k : ℕ) (u : (Jet S (Fin 2 × Fin d) m)ˣ)
    (hu : (u : Jet S (Fin 2 × Fin d) m) = psJet m (expP (-bilL B.G cc))) :
    psJet m (expP ((k : S) • diagL B w0 cc)) *
      ((Units.map (GermD.sL m (B.A.act w0)).toMonoidHom u ^ k : (Jet S (Fin 1 × Fin d) m)ˣ) :
        Jet S (Fin 1 × Fin d) m) = 1 := by
  rw [Units.val_pow_eq_pow_val, Units.coe_map]
  show psJet m _ * ((GermD.sL m (B.A.act w0)) (u : Jet S (Fin 2 × Fin d) m)) ^ k = 1
  rw [hu, jet_sL m _ (B.A.const w0), eval_expSeries_neg_bilinear, ← ExpTiePf.psJet_pow, ← FBIdJet.psJet_mul]
  unfold expP
  rw [ExpTiePf.exp_pow_inv _ (const_diagL B w0 cc) k]
  exact FBIdJet.psJet_one m
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
