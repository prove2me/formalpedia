-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA.const_hL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:43.883043+00:00
-- url     : https://prove2.me/submissions/ce042517-3b91-4086-9a23-3e469039c98f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_Sym_const_ev
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
theorem _root_.solution (C : ChartAt Xo c y) : MvPowerSeries.constantCoeff (C.B.hL S C.h H.w0) = 0 := by
  have hh0 : MvPowerSeries.constantCoeff C.h = 0 := by
    have e := Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev (n := 1) ![0, Germ.pt S (n := 1) C.d 0] (by intro p q; fin_cases p <;> simp [Germ.pt])
      C.h
    rw [C.gauge.ax0, map_zero] at e
    exact e.symm
  have hact : ∀ q, MvPowerSeries.constantCoeff (Germ.comp1 (C.B.actK S H.w0) (Germ.pt S (n := 1) C.d 0) q) = 0 := by
    intro q
    unfold Germ.comp1
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev _ (by intro p' q'; fin_cases p'; simp [Germ.pt])]
    unfold Germ.FB.actK
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, C.B.A.const, map_zero]
  unfold Germ.FB.hL
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev _ (by
    intro p q
    fin_cases p
    · simp [Germ.pt]
    · exact hact q)]
  exact hh0
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
