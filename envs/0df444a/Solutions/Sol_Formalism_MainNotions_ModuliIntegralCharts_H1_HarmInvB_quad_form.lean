-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.quad_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:48:05.276526+00:00
-- url     : https://prove2.me/submissions/8282c21b-b818-4f1d-b0c5-b6159f053c8f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB

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
theorem _root_.solution (cc : Fin d → Fin d → S) (u : Lt1 Dw → Fin d → S) (t : Fin 1 × Fin (dL Dw) → S) :
    ∑ i, ∑ l, cc i l • (linPt u (0 : Fin 1) i * MvPowerSeries.subst
      (fun q => t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (linPt u (0 : Fin 1) l)) =
    quadCol (n := 1) (qβ cc u t) := by
  have hC : ∀ (c : S) (f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S), MvPowerSeries.C c * f = c • f :=
    fun c f => by rw [MvPowerSeries.smul_eq_C_mul]
  have hT0 : ∀ q : Fin 1 × Fin (dL Dw), MvPowerSeries.constantCoeff (t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) = 0 := by
    intro q
    simp [MvPowerSeries.smul_eq_C_mul]
  have hT : MvPowerSeries.HasSubst (fun q => t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hT0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hT0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hT0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hT0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hT0 s]; exact IsNilpotent.zero)
  have hsub : ∀ l, MvPowerSeries.subst (fun q => t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (linPt u (0 : Fin 1) l) =
      ∑ ℓ, (u ℓ l * t (0, ltIdx Dw ℓ)) • (MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) := by
    intro l
    rw [← MvPowerSeries.coe_substAlgHom hT]
    simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.linPt, hC, map_sum, map_smul]
    simp only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hT, smul_smul]
  have hlin : ∀ i, linPt u (0 : Fin 1) i = ∑ ℓ, u ℓ i • (MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) := by
    intro i
    simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.linPt, hC]
  have key : ∀ {M : Type} [AddCommMonoid M] (F : Fin d → Fin d → Lt1 Dw → Lt1 Dw → M),
      ∑ ℓ, ∑ ℓ', ∑ i, ∑ l, F i l ℓ ℓ' = ∑ i, ∑ l, ∑ ℓ, ∑ ℓ', F i l ℓ ℓ' := by
    intro M _ F
    calc ∑ ℓ, ∑ ℓ', ∑ i, ∑ l, F i l ℓ ℓ' = ∑ ℓ, ∑ i, ∑ ℓ', ∑ l, F i l ℓ ℓ' :=
          Finset.sum_congr rfl (fun ℓ _ => Finset.sum_comm)
      _ = ∑ i, ∑ ℓ, ∑ ℓ', ∑ l, F i l ℓ ℓ' := Finset.sum_comm
      _ = ∑ i, ∑ ℓ, ∑ l, ∑ ℓ', F i l ℓ ℓ' :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun ℓ _ => Finset.sum_comm))
      _ = ∑ i, ∑ l, ∑ ℓ, ∑ ℓ', F i l ℓ ℓ' :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  have hR : quadCol (n := 1) (qβ cc u t) = ∑ i, ∑ l, ∑ ℓ, ∑ ℓ', (cc i l * u ℓ i * u ℓ' l * t (0, ltIdx Dw ℓ')) •
      ((MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) * (MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ') : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) := by
    rw [← key]
    simp only [ReciprocityTheory.ChartRestriction.G.TB.quadCol, Fin.sum_univ_one, mul_assoc, hC]
    rw [← (ltIdx Dw).sum_comp]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [← (ltIdx Dw).sum_comp]
    refine Finset.sum_congr rfl (fun ℓ' _ => ?_)
    simp only [qβ, Equiv.symm_apply_apply, Finset.sum_smul, mul_assoc, Finset.sum_mul, smul_mul_assoc]
  rw [hR]
  simp only [hsub]
  simp only [hlin]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  first
  | simp only [smul_mul_smul_comm, Finset.smul_sum, smul_smul]
  | simp only [smul_mul_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun ℓ _ => Finset.sum_congr rfl (fun ℓ' _ => ?_))))
  congr 1
  ring
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
