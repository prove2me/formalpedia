-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.scaled_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:23:21.576776+00:00
-- url     : https://prove2.me/submissions/c310ee1e-abea-44a6-9d0a-835df5d63987

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqH
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA

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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {X Y Z : Scheme.{0}} (L : LB X)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution {M : LB Y} (t t' : LB.Gen M) (u : Γ(Y, ⊤)ˣ)
    (h : IsScaled u t t') (k : ℕ) :
    IsScaled (u ^ k) (⟨fun j => t.s j ^ k⟩ : LB.Gen M) ⟨fun j => t'.s j ^ k⟩ := by
  intro j
  show t'.s j ^ k = res le_top (u ^ k) * t.s j ^ k
  rw [h j, mul_pow, map_pow]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
