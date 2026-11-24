-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.atPt_expPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:25.319811+00:00
-- url     : https://prove2.me/submissions/f229a805-c625-46b3-9e2d-bde64d7f7915

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_subst_linPt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_hasSubst_linPt

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
theorem _root_.solution (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (b : Fin 2) (i : Fin d) :
    atPt b (expPhi uvec ε i) = subst (fun q : Fin 1 × Fin d => linPt uvec b q.2) (ε i) := by
  have hb : HasSubst (fun q : Fin 1 × Fin (dL Dw) => (X (b, q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    hasSubst_of_constantCoeff_zero fun q => by simp
  rw [atPt, expPhi, subst_comp_subst_apply (hasSubst_linPt uvec 0) hb]
  congr 1
  funext q
  rw [subst_linPt uvec 0 _ hb, linPt]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
