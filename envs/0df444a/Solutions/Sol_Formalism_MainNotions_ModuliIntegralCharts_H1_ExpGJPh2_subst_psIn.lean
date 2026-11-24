-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2.subst_psIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:43:08.825719+00:00
-- url     : https://prove2.me/submissions/e084ace0-e0f3-4681-97d4-ca2bac298ceb

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhTwoValHolds
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_psJet_subst_trunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
private theorem subst_rename_lemma {σ τ υ R : Type} [CommRing R] [Finite σ] [Finite τ]
    (a : σ → MvPowerSeries υ R) (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ρ : τ → σ)
    (q : MvPolynomial τ R) :
    MvPowerSeries.subst a ((MvPolynomial.rename ρ q : MvPolynomial σ R) : MvPowerSeries σ R) =
      MvPowerSeries.subst (fun t => a (ρ t)) (q : MvPowerSeries τ R) := by
  have h1 : MvPowerSeries.HasSubst a := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  have h2 : MvPowerSeries.HasSubst (fun t => a (ρ t)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => ha (ρ t))
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [(fun t => ha (ρ t)) s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [(fun t => ha (ρ t)) s]; exact IsNilpotent.zero)
  rw [← MvPowerSeries.coe_substAlgHom h1, ← MvPowerSeries.coe_substAlgHom h2]
  erw [MvPowerSeries.substAlgHom_coe, MvPowerSeries.substAlgHom_coe, MvPolynomial.aeval_rename]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
attribute [local instance] Over.cartesianMonoidalCategory
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
theorem _root_.solution {d n n' : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (r : Fin n → Fin n')
    (Q : Fin n' × Fin d → MvPowerSeries κ S) (hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0)
    (f : MvPowerSeries (Fin n × Fin d) S) :
    psJet m (MvPowerSeries.subst Q ((psIn d m r f : MvPolynomial _ S) : MvPowerSeries _ S)) =
      psJet m (MvPowerSeries.subst (fun p : Fin n × Fin d => Q (r p.1, p.2)) f) := by
  simp only [psIn]
  rw [subst_rename_lemma Q hQ, ExpGF.psJet_subst_trunc m _ (fun _ => hQ _) f]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
