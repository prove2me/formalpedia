-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG.actPS_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:20.145953+00:00
-- url     : https://prove2.me/submissions/6e8a0c79-4177-4383-a117-1cb35fb348c5

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_hasSubst_actPS

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
open MvPowerSeries NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
theorem _root_.solution (u v : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    subst (actPS (Dw := Dw) (S := S) c v) (actPS (Dw := Dw) (S := S) c u q) = actPS (Dw := Dw) (S := S) c (u * v) q := by
  have hv := hasSubst_actPS (Dw := Dw) (S := S) c v
  have e : actPS (Dw := Dw) (S := S) c u q =
      algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 u) • MvPowerSeries.X q := rfl
  rw [e, subst_smul hv, subst_X hv]
  simp only [actPS, smul_smul, map_mul]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
