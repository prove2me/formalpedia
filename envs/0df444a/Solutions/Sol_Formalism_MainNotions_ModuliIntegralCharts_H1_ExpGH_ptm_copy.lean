-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH.ptm_copy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:00.980234+00:00
-- url     : https://prove2.me/submissions/3a06d868-a1d4-4edc-a691-15bd35947d58

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetCopy_eq_PS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetSubstPS_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero


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
theorem _root_.solution (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ) (i : Fin n) :
    ptm C P m ≫ homAt y.x (jetCopy C.d m i) = ptm C ![P i] m := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin n × Fin C.d => P p.1 p.2) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [(fun p => hP p.1 p.2) q]; exact IsNilpotent.zero)
  unfold ptm
  rw [GermD.homAt_comp, ExpGF.jetCopy_eq_PS,
    ExpGF.jetSubstPS_comp m (fun p : Fin 1 × Fin C.d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin C.d) S))
      (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => MvPowerSeries.constantCoeff_X _) (fun p => hP p.1 p.2)]
  refine congrArg (homAt y.x) (congrArg (jetSubstPS (m := m)) ?_)
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  simp [MvPowerSeries.subst_X hs]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
