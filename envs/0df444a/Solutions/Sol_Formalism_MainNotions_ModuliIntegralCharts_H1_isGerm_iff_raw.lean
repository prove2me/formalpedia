-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.isGerm_iff_raw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:48:01.43719+00:00
-- url     : https://prove2.me/submissions/f617efc0-a0e8-4aa7-986f-caa67778646e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndRaw

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPolynomial (X C)
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    IsGerm y d x act e wP k F f ↔ RIsGerm y.x d x act e wP k F f := Iff.rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1
