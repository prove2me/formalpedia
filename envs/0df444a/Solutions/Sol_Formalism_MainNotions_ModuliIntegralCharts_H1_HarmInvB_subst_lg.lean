-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.subst_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:54.371862+00:00
-- url     : https://prove2.me/submissions/beb5f09c-a363-4eb5-88e9-18f14c770063

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
theorem _root_.solution (G : FGLaw S d) {τ : Type} (Bφ : Fin 2 × Fin d → MvPowerSeries τ S)
    (hB : ∀ p, MvPowerSeries.constantCoeff (Bφ p) = 0) (j : Fin 2) (i : Fin d) :
    MvPowerSeries.subst Bφ (lg G j i) = MvPowerSeries.subst (fun p : Fin 1 × Fin d => Bφ (j, p.2)) (logOf G i) := by
  have h0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (![pt S (n := 2) d j] p.1 p.2 : MvPowerSeries (Fin 2 × Fin d) S) = 0 := by
    intro p
    rcases p with ⟨a, c⟩
    rw [Subsingleton.elim a 0]
    simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  have hA : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => (![pt S (n := 2) d j] p.1 p.2 : MvPowerSeries (Fin 2 × Fin d) S)) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero h0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
  have hBs : MvPowerSeries.HasSubst Bφ := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hB
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hB
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hB
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hB s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hB s]; exact IsNilpotent.zero)
  change MvPowerSeries.subst Bφ (MvPowerSeries.subst (fun p : Fin 1 × Fin d => (![pt S (n := 2) d j] p.1 p.2 : MvPowerSeries (Fin 2 × Fin d) S)) (logOf G i)) = _
  rw [MvPowerSeries.subst_comp_subst_apply hA hBs]
  congr 1
  funext p
  rcases p with ⟨a, c⟩
  rw [Subsingleton.elim a 0]
  simp only [Matrix.cons_val_zero, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, MvPowerSeries.subst_X hBs]
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
