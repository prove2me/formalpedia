-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.log_expPhi_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:48:04.451975+00:00
-- url     : https://prove2.me/submissions/b5ec808c-3361-46a0-90e3-0e0d1ae33c54

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvB_log_expPhi
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_expPhi_const


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
theorem _root_.solution (G : FGLaw S d) (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d)
    (hinv : IsInvPair ε (fun i => logOf G i)) (a : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (ha : ∀ q, MvPowerSeries.constantCoeff (a q) = 0) (i : Fin d) :
    MvPowerSeries.subst (fun p : Fin 1 × Fin d => MvPowerSeries.subst a (expPhi uvec ε p.2)) (logOf G i) =
      MvPowerSeries.subst a (linPt uvec (0 : Fin 1) i) := by
  have hε0 : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0 := by
    obtain ⟨h, -⟩ := hinv
    exact h
  have hE0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (expPhi uvec ε p.2) = 0 :=
    fun p => Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.expPhi_const uvec ε hε0 p.2
  have hE : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hE0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hE0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hE0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hE0 s]; exact IsNilpotent.zero)
  have ha' : MvPowerSeries.HasSubst a := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  rw [← MvPowerSeries.subst_comp_subst_apply hE ha', log_expPhi G uvec ε hinv i]
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
