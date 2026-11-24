-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.const_compL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:03.478546+00:00
-- url     : https://prove2.me/submissions/4c578993-d5f7-4fd7-9db5-c18bef9ca7f0

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
theorem _root_.solution {d' : ℕ} (φ : Fin d' → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (g : MvPowerSeries (Fin 1 × Fin d') S) :
    MvPowerSeries.constantCoeff (compL φ g) = MvPowerSeries.constantCoeff g := by
  have ha : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d' => φ p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hφ p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => hφ p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hφ p.2]; exact IsNilpotent.zero)
  unfold compL
  rw [MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hd (Finsupp.ext hcon)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (φ s.2) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hi) (by rw [map_pow, hφ, zero_pow hi])
    simp only [h0, smul_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
