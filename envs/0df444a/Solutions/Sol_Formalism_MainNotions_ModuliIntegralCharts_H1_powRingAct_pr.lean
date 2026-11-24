-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.powRingAct_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:33.06635+00:00
-- url     : https://prove2.me/submissions/61e43476-975f-463d-b056-8d2b54c88b7e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GPowSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GPowPf

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A' A : Over S} [GrpObj A'] [GrpObj A] {n : ℕ}
variable [IsCommMonObj A'] [IsCommMonObj A]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution (p : IsPowGrp A' A n) {O : Type} [Ring O] (ρ : RingAct A O) (a : O) (i : Fin n) :
    (powRingAct p ρ).act a ≫ p.pr i = p.pr i ≫ ρ.act a :=
  powMap_pr p _ i
end Formalism.MainNotions.ModuliIntegralCharts.H1
