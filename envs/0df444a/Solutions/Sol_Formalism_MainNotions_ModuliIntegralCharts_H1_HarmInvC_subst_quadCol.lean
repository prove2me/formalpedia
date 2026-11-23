-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.subst_quadCol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:30.215082+00:00
-- url     : https://prove2.me/submissions/bc5fd353-3321-45e7-ab71-02e52b70b50e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddFin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvC
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_sb_cc

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
variable {S : Type} [CommRing S] {n d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
theorem _root_.solution (b : Fin n) (r : S) (β : Matrix (Fin d) (Fin d) S) :
    MvPowerSeries.subst (sb b) (r • TB.quadCol (n := 1) β) =
      r • ∑ i : Fin d, ∑ j : Fin d, MvPowerSeries.C (β i j) * MvPowerSeries.X (b, i) * MvPowerSeries.X (b, j) := by
  have h0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (sb (S := S) (n := n) (d := d) b p) = 0 := fun p => sb_cc b p
  have hs : MvPowerSeries.HasSubst (sb (S := S) (n := n) (d := d) b) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero h0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
  have hC : ∀ (c : S) (f : MvPowerSeries (Fin 1 × Fin d) S), MvPowerSeries.C c * f = c • f :=
    fun c f => by rw [MvPowerSeries.smul_eq_C_mul]
  have hC' : ∀ (c : S) (f : MvPowerSeries (Fin n × Fin d) S), MvPowerSeries.C c * f = c • f :=
    fun c f => by rw [MvPowerSeries.smul_eq_C_mul]
  rw [← MvPowerSeries.coe_substAlgHom hs]
  simp only [ReciprocityTheory.ChartRestriction.G.TB.quadCol, Fin.sum_univ_one, mul_assoc, hC, hC', map_smul, map_sum, map_mul]
  simp only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hs, sb]
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
