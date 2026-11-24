-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParE.ParEFormula_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:58.737422+00:00
-- url     : https://prove2.me/submissions/ffceef81-d175-41e6-b42a-a32b356e647d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassSeriesIntegral
import Theorems.Thm_Formalism_L2_Th1_B_ParE_subst_phE
import Theorems.Thm_Formalism_L2_Th1_B_ParE_subst_inVar
import Theorems.Thm_Formalism_L2_Th1_B_ParE_subst_parallelogram_defect
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_iff_lift
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_B_law_constantCoeff_FI
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_one__f427d3a2f5d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.ParE
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)
section Alg
variable {K : Type} [Field K] [CharZero K] {ι : Type}
end Alg
private theorem cc_subst_lemma {R : Type*} [CommRing R] {τ : Type*} {a : MvPowerSeries τ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ha), map_mul, ha, zero_mul]
private theorem mvSubst_powerSeries_subst_eq_subst_mvSubst {R : Type*} [CommRing R] {σ τ : Type*} {c : σ → MvPowerSeries τ R}
    (hc : MvPowerSeries.HasSubst c) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries R) :
    MvPowerSeries.subst c (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst c a) f :=
  MvPowerSeries.subst_comp_subst_apply
    (⟨fun _ => by simp [ha, IsNilpotent.zero], fun _ => Set.toFinite _⟩ :
      MvPowerSeries.HasSubst (fun _ : Unit => a)) hc f
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type}
end Norm
end Formalism.L2.Th1.B.ParE
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParE
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)
namespace Formalism.L2.Th1.B.ParE
theorem _root_.solution (hA : AddSigma1Log) : ParEFormula := by
  intro K _ _ _ A kap e1 s2 w l i F hW hLL hI
  have hat : ∀ (x : Fin 2) (f : PowerSeries K), at1 x f = PowerSeries.subst (MvPowerSeries.X x) f :=
    fun _ _ => rfl
  have hl0 : PowerSeries.constantCoeff l = 0 := hLL.2.2.1
  have hx0 : ∀ x : Fin 2, MvPowerSeries.constantCoeff (at1 x l) = 0 := fun x => by
    rw [hat]
    exact cc_subst_lemma (MvPowerSeries.constantCoeff_X x) hl0
  have L1 : PowerSeries.subst F l = at1 (0 : Fin 2) l + at1 (1 : Fin 2) l := by
    have h := hLL.2.2.2.2
    unfold cob at h
    linear_combination h
  have L2 : PowerSeries.subst (FI F i) l = at1 (0 : Fin 2) l - at1 (1 : Fin 2) l := by
    have hci : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) i) = 0 := by
      rw [hat]
      exact cc_subst_lemma (MvPowerSeries.constantCoeff_X 1) hI.1
    have hc : MvPowerSeries.HasSubst ![(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K), at1 (1 : Fin 2) i] :=
      ⟨fun s => by fin_cases s <;> simp [hci, IsNilpotent.zero], fun _ => Set.toFinite _⟩
    have hneg : at1 (1 : Fin 2) (-l) = -at1 (1 : Fin 2) l := by
      rw [hat, hat, ← PowerSeries.coe_substAlgHom
        (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X (1 : Fin 2))), map_neg]
    unfold FI
    rw [← mvSubst_powerSeries_subst_eq_subst_mvSubst hc hLL.1 l, L1, ← MvPowerSeries.coe_substAlgHom hc, map_add,
      MvPowerSeries.coe_substAlgHom hc, hat 0 l, hat 1 l,
      mvSubst_powerSeries_subst_eq_subst_mvSubst hc (MvPowerSeries.constantCoeff_X 0) l, mvSubst_powerSeries_subst_eq_subst_mvSubst hc (MvPowerSeries.constantCoeff_X 1) l,
      MvPowerSeries.subst_X hc, MvPowerSeries.subst_X hc]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [← subst_inVar (1 : Fin 2) l hI.1, hI.2.2, hneg, hat 1 l]
    ring
  have hP : PowerSeries.subst (at1 (0 : Fin 2) l + at1 (1 : Fin 2) l) (sigmaOneSeries e1 kap w) +
      PowerSeries.subst (at1 (0 : Fin 2) l - at1 (1 : Fin 2) l) (sigmaOneSeries e1 kap w) -
      2 * PowerSeries.subst (at1 (0 : Fin 2) l) (sigmaOneSeries e1 kap w) - 2 * PowerSeries.subst (at1 (1 : Fin 2) l) (sigmaOneSeries e1 kap w) =
      MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 (1 : Fin 2) l] (fLog (1 - MvPowerSeries.C kap * at1 (0 : Fin 2) w * at1 (1 : Fin 2) w)) := by
    rw [← hA K A kap e1 w hW, subst_parallelogram_defect _ (hx0 0) (hx0 1)]
  have hFL : MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 (1 : Fin 2) l] (fLog (1 - MvPowerSeries.C kap * at1 (0 : Fin 2) w * at1 (1 : Fin 2) w)) =
      fLog (1 - MvPowerSeries.C kap * at1 (0 : Fin 2) (PowerSeries.subst l w) * at1 (1 : Fin 2) (PowerSeries.subst l w)) := by
    have hab : MvPowerSeries.HasSubst ![at1 (0 : Fin 2) l, at1 (1 : Fin 2) l] :=
      ⟨fun s => by fin_cases s <;> simp [hx0, IsNilpotent.zero], fun _ => Set.toFinite _⟩
    have hw0 : ∀ x : Fin 2, MvPowerSeries.constantCoeff (at1 x w) = 0 := fun x => by
      rw [hat]
      exact cc_subst_lemma (MvPowerSeries.constantCoeff_X x) hW.1
    have hg : MvPowerSeries.constantCoeff
        ((1 : MvPowerSeries (Fin 2) K) - MvPowerSeries.C kap * at1 (0 : Fin 2) w * at1 (1 : Fin 2) w - 1) = 0 := by
      rw [map_sub, map_sub, map_one, map_mul, map_mul, hw0 0, hw0 1]
      simp
    have hCk : MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 (1 : Fin 2) l] (MvPowerSeries.C kap : MvPowerSeries (Fin 2) K) =
        MvPowerSeries.C kap := by
      have h := (MvPowerSeries.substAlgHom hab).commutes kap
      rw [MvPowerSeries.coe_substAlgHom] at h
      simpa [MvPowerSeries.algebraMap_apply] using h
    have hw : ∀ x : Fin 2, MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 (1 : Fin 2) l] (at1 x w) = at1 x (PowerSeries.subst l w) := by
      intro x
      rw [hat x w, mvSubst_powerSeries_subst_eq_subst_mvSubst hab (MvPowerSeries.constantCoeff_X x) w, MvPowerSeries.subst_X hab,
        subst_inVar x w hl0]
      fin_cases x <;> simp
    unfold fLog
    rw [mvSubst_powerSeries_subst_eq_subst_mvSubst hab hg, ← MvPowerSeries.coe_substAlgHom hab]
    simp only [map_sub, map_one, map_mul]
    rw [MvPowerSeries.coe_substAlgHom hab, hCk, hw 0, hw 1]
  unfold par
  rw [subst_phE s2 e1 kap w hl0 hLL.1, L1, subst_phE s2 e1 kap w hl0 (law_constantCoeff_FI hLL hI), L2,
    hat 0 (phE s2 e1 kap w l), hat 1 (phE s2 e1 kap w l),
    subst_phE s2 e1 kap w hl0 (MvPowerSeries.constantCoeff_X (0 : Fin 2)),
    subst_phE s2 e1 kap w hl0 (MvPowerSeries.constantCoeff_X (1 : Fin 2)), ← hat 0 l, ← hat 1 l]
  linear_combination -hP - hFL
end Formalism.L2.Th1.B.ParE
