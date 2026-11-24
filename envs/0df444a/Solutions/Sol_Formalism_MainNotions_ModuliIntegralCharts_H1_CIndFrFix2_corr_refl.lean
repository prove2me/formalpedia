-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.corr_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:48.878071+00:00
-- url     : https://prove2.me/submissions/151d94b8-b52f-4137-894e-99f44b085d2e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MvPolynomial (X)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
theorem _root_.solution {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ ε g g := by
  intro j j' _ _ hx
  have : j = j' := funext fun k => hx k k rfl
  subst this
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
