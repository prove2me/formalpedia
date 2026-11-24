-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.tw_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:51.411395+00:00
-- url     : https://prove2.me/submissions/5e447188-9a59-4150-9a43-fcd186b3f3f6

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378


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
theorem _root_.solution (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) (hg : (e m).IsGen) :
    (tw y d x e T m).IsGen := by
  intro i j
  have h := hg i j
  unfold tw scaleGen
  dsimp only
  erw [map_mul, map_mul, ReciprocityTheory.ChartRestriction.G.DVR.res_res', ReciprocityTheory.ChartRestriction.G.DVR.res_res', h]
  all_goals first | exact mul_left_comm _ _ _ | exact le_rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
