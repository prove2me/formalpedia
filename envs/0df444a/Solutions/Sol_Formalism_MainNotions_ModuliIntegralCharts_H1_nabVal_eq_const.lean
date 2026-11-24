-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.nabVal_eq_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:31.901213+00:00
-- url     : https://prove2.me/submissions/871c0793-e0fb-4cb9-be1c-fea29d307f61

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj ExpTieAlg NumberField
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    (B : FB S d O) (h : PS S 2 d) (w0 : O) (k : ℕ) (f : PS S 1 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S)
    (P : MvPolynomial κ S) :
    B.nabVal S h w0 k f u P = constantCoeff (DpolyOf B.G.F u P (f * FB.expS S ((k : S) • B.hL S h w0))) := by
  first
  | rfl
  | (simp only [FB.nabVal, FB.FK]; rfl)
end Formalism.MainNotions.ModuliIntegralCharts.H1
