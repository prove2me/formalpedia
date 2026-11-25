-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.alg1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:49.567513+00:00
-- url     : https://prove2.me/submissions/e4d49c98-3a8f-482b-8b8f-04598d151a5f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
theorem _root_.solution {M : Type} [CommGroup M] (W b1 b2 b3 g1 g2 g3 : M)
    (h : W * (b1 * (b2⁻¹ * b3⁻¹)) = W * (g1 * b1 * ((g2 * b2)⁻¹ * (g3 * b3)⁻¹))) : g1 = g2 * g3 := by
  have h' := mul_left_cancel h
  have hr : g1 * b1 * ((g2 * b2)⁻¹ * (g3 * b3)⁻¹) = (g1 * (g2 * g3)⁻¹) * (b1 * (b2⁻¹ * b3⁻¹)) := by
    simp only [mul_inv]
    ac_rfl
  rw [hr] at h'
  have h1 : g1 * (g2 * g3)⁻¹ = 1 := by
    apply mul_right_cancel (b := b1 * (b2⁻¹ * b3⁻¹))
    rw [_root_.one_mul]
    exact h'.symm
  exact mul_inv_eq_one.mp h1
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
