-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH.exp_chart_action_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:08:24.418993+00:00
-- url     : https://prove2.me/submissions/efa8b80e-dcfc-468b-8143-7c198fbeb97a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_sA_ptm
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_j__eq_fd4b82769420

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (hx : IsExpChart y (xExp y C φ)) (m : ℕ) (u : 𝓞 E) :
    xExp y C φ m ≫ Xo.univ.t.act.act u = ptm C ![φa c φ u] m ≫ C.x m := by
  have hP : ∀ i j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0 := by
    intro i j
    fin_cases i
    exact hφ j
  have e : (fun i j => MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c u) ((![φ] : Fin 1 → _) i j)) =
      ![φa c φ u] := by
    funext i j
    fin_cases i
    rfl
  rw [hx.act m u, xExp, ← Category.assoc, jφ_eq, sA_ptm C _ hP m u, e]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
