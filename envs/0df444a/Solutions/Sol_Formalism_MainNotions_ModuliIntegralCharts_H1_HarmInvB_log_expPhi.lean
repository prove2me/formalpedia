-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.log_expPhi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:43.775872+00:00
-- url     : https://prove2.me/submissions/e93c073c-b4d0-4d87-8ddb-9a74f1a858c8

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
theorem _root_.solution (G : FGLaw S d) (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d)
    (hinv : IsInvPair ε (fun i => logOf G i)) (i : Fin d) :
    MvPowerSeries.subst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) (logOf G i) = linPt uvec (0 : Fin 1) i := by
  obtain ⟨hε0, -, -, hcomp⟩ := hinv
  have h1 := congrFun hcomp i
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.comp1, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt] at h1
  have hε : (fun p : Fin 1 × Fin d => (![ε] p.1 p.2 : MvPowerSeries (Fin 1 × Fin d) S)) = fun p => ε p.2 := by
    funext p
    rcases p with ⟨a, c⟩
    rw [Subsingleton.elim a 0]
    rfl
  rw [hε] at h1
  have h0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (ε p.2) = 0 := fun p => hε0 p.2
  have hA : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => ε p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero h0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
  have hL0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (linPt uvec (0 : Fin 1) p.2) = 0 := by
    intro p
    simp [Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.linPt]
  have hL : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => linPt uvec (0 : Fin 1) p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hL0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hL0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hL0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hL0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hL0 s]; exact IsNilpotent.zero)
  change MvPowerSeries.subst (fun p : Fin 1 × Fin d => MvPowerSeries.subst (fun q : Fin 1 × Fin d => linPt uvec (0 : Fin 1) q.2) (ε p.2)) (logOf G i) = _
  rw [← MvPowerSeries.subst_comp_subst_apply hA hL, h1, MvPowerSeries.subst_X hL]
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
