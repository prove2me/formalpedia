-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA.exists_uJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:50.909368+00:00
-- url     : https://prove2.me/submissions/067a09fe-f58f-42c8-a98f-2c8dc2af98c5

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGA_const_hL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_Sym_const_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_const_subst


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
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (m : ℕ) :
    ∃ u : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
      (u : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) := by
  have h0 : MvPowerSeries.constantCoeff (compL φ (C.B.hL S C.h H.w0)) = 0 := by
    unfold compL
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.const_subst (fun p : Fin 1 × Fin C.d => hφ p.2)]
    exact const_hL C
  have h1 : MvPowerSeries.constantCoeff (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) = 1 := by
    unfold Germ.FB.expS
    rw [PowerSeries.subst, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.const_subst (fun _ => by rw [map_neg, h0, neg_zero])]
    exact PowerSeries.constantCoeff_exp
  obtain ⟨v, hv⟩ : IsUnit (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [h1]; exact isUnit_one)
  refine ⟨⟨psJet m (v : MvPowerSeries _ S), psJet m (↑v⁻¹ : MvPowerSeries _ S), ?_, ?_⟩, ?_⟩
  · rw [← FBIdJet.psJet_mul, Units.mul_inv, FBIdJet.psJet_one]
  · rw [← FBIdJet.psJet_mul, Units.inv_mul, FBIdJet.psJet_one]
  · simp only [hv]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
