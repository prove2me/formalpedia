-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.tw_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:42:36.315153+00:00
-- url     : https://prove2.me/submissions/ff4767a9-f23f-43b8-9492-d6cda531c610

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_scaleGenG_one
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__one_93204f7b6736


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
theorem _root_.solution (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (h0 : T 0 = 1) :
    tw y d x e T 0 = e 0 := by
  have h1 := FBIdLB.scaleGenG_one Xo.univ.t (cφ ![jpt y d x 0 (0 : Fin 2), jpt y d x 0 (1 : Fin 2)]) (cε 2) (e 0)
  have h2 : unitΓ (T 0) = 1 := by rw [h0, FBIdSy.unitΓ_one]
  show scaleGenG Xo.univ.t _ _ (unitΓ (T 0)) (e 0) = e 0
  rw [h2]
  exact h1
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
