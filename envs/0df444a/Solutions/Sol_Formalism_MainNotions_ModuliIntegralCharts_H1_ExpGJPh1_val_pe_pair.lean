-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1.val_pe_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:06:55.183988+00:00
-- url     : https://prove2.me/submissions/b831aef8-0085-4ddd-bec3-eaf1ed795655

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SubstCoeRename
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_const_substPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1
theorem _root_.solution (C : ChartAt Xo c y) (m : ℕ) (P3 : Fin 3 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP3c : ∀ i j, MvPowerSeries.constantCoeff (P3 i j) = 0)
    (σ : Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) (hσ : ∀ i j, MvPolynomial.constantCoeff (σ i j) = 0)
    (Q : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hQ : ∀ i j, MvPowerSeries.constantCoeff (Q i j) = 0)
    (hs : ∀ i j, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
      ((σ i j : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) = psJet m (Q i j))
    {z : (jO y (dL Dw) m 1).left} {J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι}
    (hJ : Good Xo.univ.t.PP.L z J) :
    val (pe y C.d C.x C.e m σ) (ptm C P3 m).left z J = val (C.e m) (ptm C Q m).left z J := by
  refine (show val (pe y C.d C.x C.e m σ) (ptm C P3 m).left z J = val (C.e m)
      ((ptm C P3 m).left ≫ (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d => σ p.1 p.2)).left) z J from
    val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, ptm_subst C P3 hP3c m (fun p : Fin 2 × Fin C.d => σ p.1 p.2) (fun p => hσ p.1 p.2)]
  rw [ptm_congr C (fun i j => const_substPS (fun p : Fin 3 × Fin C.d => P3 p.1 p.2) (fun p => hP3c p.1 p.2) _ (by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]; exact hσ i j)) hQ m hs]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1
