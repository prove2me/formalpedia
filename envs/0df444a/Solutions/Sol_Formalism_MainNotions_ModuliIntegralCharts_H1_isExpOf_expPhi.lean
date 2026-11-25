-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.isExpOf_expPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:27:19.655015+00:00
-- url     : https://prove2.me/submissions/5be42f46-1dc8-4b50-950c-a37e9af5993a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_dLin_inv
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_expPhi_const
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_expPhi_lin
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_expPhi_hom
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution {S : Type} [CommRing S] [Algebra ℚ S] {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {d : ℕ} (G : FGLaw S d) (uvec : Lt1 Dw → Fin d → S) (ℓ ε : Pt S 1 d)
    (hℓ1 : dLin ℓ = 1) (hinv : IsInvPair ε ℓ)
    (htr : transF G.F ε ℓ = pt S (n := 2) d 0 + pt S (n := 2) d 1) :
    IsExpOf G.F uvec (ExpOf.expPhi uvec ε) :=
  ⟨ExpOf.expPhi_const uvec ε hinv.1, fun ℓ' j => ExpOf.expPhi_lin uvec ε (ExpOf.dLin_inv ℓ ε hℓ1 hinv) ℓ' j,
    fun j => ExpOf.expPhi_hom G uvec ℓ ε hinv htr j⟩
end Formalism.MainNotions.ModuliIntegralCharts.H1
