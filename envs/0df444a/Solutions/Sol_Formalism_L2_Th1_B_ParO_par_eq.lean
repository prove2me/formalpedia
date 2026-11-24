-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.par_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:29:01.233128+00:00
-- url     : https://prove2.me/submissions/65e46453-18e5-4773-8c23-5531815144d1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_fExp_mul_neg
import Theorems.Thm_Formalism_L2_Th1_B_ParO_subst_inVar
import Theorems.Thm_Formalism_L2_Th1_B_ParO_constantCoeff_inVar
import Theorems.Thm_Formalism_L2_Th1_B_ParO_value_at
import Theorems.Thm_Formalism_L2_Th1_B_ParO_inVar_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_inVar_add_inVar_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_inVar_sub_inVar_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_ne_zero_of_psubst
import Theorems.Thm_Formalism_L2_Th1_B_ParO_subst_atS
import Theorems.Thm_Formalism_L2_Th1_B_ParO_subst_atD
import Theorems.Thm_Formalism_L2_Th1_B_ParO_subst_wpDiff
import Theorems.Thm_Formalism_L2_Th1_B_ParO_curve_at
import Theorems.Thm_Formalism_L2_Th1_B_ParO_log_law
import Theorems.Thm_Formalism_L2_Th1_B_ParO_constantCoeff_FI
import Theorems.Thm_Formalism_L2_Th1_B_ParO_log_FI
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add
import Theorems.Thm_Formalism_L2_Th1_B_fLog_fExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.ParO
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
section Alg
variable {K : Type} [Field K] [CharZero K]
private theorem constantCoeff_vec_pair_eq_zero {ι : Type} {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    ∀ s : Fin 2, MvPowerSeries.constantCoeff (![a, b] s) = 0 :=
  Fin.forall_fin_two.mpr ⟨ha, hb⟩
end Alg
section Norm
variable {K : Type} [NormedField K] [CharZero K]
private theorem addition_identity_products_eq_neg_c_mul_sq {R : Type} [CommRing R] [NoZeroDivisors R]
    {L0 L1 X0 X1 F D c EF ED E0 E1 P0 P1 ep0 ep1 c0 : R}
    (hN : L0 ^ 2 * L1 ^ 2 * F * D ≠ 0)
    (KE : L0 ^ 2 * L1 ^ 2 * (F * EF * (D * ED)) =
      (X0 * E0) ^ 2 * (X1 * E1) ^ 2 * (L0 ^ 2 - L1 ^ 2 + L0 ^ 2 * L1 ^ 2 * (P1 - P0)))
    (C0 : X0 ^ 2 * (1 + L0 ^ 2 * P0) = L0 ^ 2 * (ep0 + c0 * X0 ^ 2))
    (C1 : X1 ^ 2 * (1 + L1 ^ 2 * P1) = L1 ^ 2 * (ep1 + c0 * X1 ^ 2))
    (hc : X1 ^ 2 * ep0 - X0 ^ 2 * ep1 = c * F * D) :
    EF * ED = -c * E0 ^ 2 * E1 ^ 2 := by
  have W : X0 ^ 2 * X1 ^ 2 * (L0 ^ 2 - L1 ^ 2 + L0 ^ 2 * L1 ^ 2 * (P1 - P0)) =
      -(L0 ^ 2 * L1 ^ 2 * c * F * D) := by
    linear_combination (-(L0 ^ 2 * L1 ^ 2)) * hc + (X0 ^ 2 * L0 ^ 2) * C1 - (X1 ^ 2 * L1 ^ 2) * C0
  apply mul_left_cancel₀ hN
  linear_combination KE + (E0 ^ 2 * E1 ^ 2) * W
end Norm
section Alg2
variable {K : Type} [Field K] [CharZero K]
end Alg2
end Formalism.L2.Th1.B.ParO
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParO
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
variable {K : Type} [NormedField K] [CharZero K]
namespace Formalism.L2.Th1.B.ParO
theorem _root_.solution (hA : AddSgStar) (hD : PhODef) {g2 g3 s2 c0 : K} {P l i ep : PowerSeries K}
    {F c : MvPowerSeries (Fin 2) K} (hP : IsWp g2 g3 P) (hF : LawLog F l) (hi : IsInv l i)
    (h3 : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2))
    (hc : MvPowerSeries.X 1 ^ 2 * at1 0 ep - MvPowerSeries.X 0 ^ 2 * at1 1 ep = c * F * FI F i) :
    par F i (phO s2 P l) = -fLog (-c) := by
  have hl0 : PowerSeries.constantCoeff l = 0 := hF.2.2.1
  have hl1 : PowerSeries.coeff 1 l = 1 := hF.2.2.2.1
  have hF0 : MvPowerSeries.constantCoeff F = 0 := hF.1
  have hD0 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.FI F i) = 0 := constantCoeff_FI hF hi
  obtain ⟨hψ0, e⟩ := hD K s2 P l hl0 hl1
  have hAd := hA K g2 g3 s2 P hP
  have hL0c : MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_inVar 0 hl0
  have hL1c : MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 1 l : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_inVar 1 hl0
  have hb : MvPowerSeries.HasSubst ![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vec_pair_eq_zero hL0c hL1c)
  have hb0 : (![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] : Fin 2 → MvPowerSeries (Fin 2) K) 0 =
      Formalism.InvariantFactorPaths.G7.at1 0 l := rfl
  have hb1 : (![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] : Fin 2 → MvPowerSeries (Fin 2) K) 1 =
      Formalism.InvariantFactorPaths.G7.at1 1 l := rfl
  have KE := congrArg
    (fun φ => MvPowerSeries.subst ![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] φ) hAd
  simp only [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_pow hb, MvPowerSeries.subst_X hb,
    subst_atS (Formalism.L2.Th1.B.sgStar s2 P) hb, subst_atD (Formalism.L2.Th1.B.sgStar s2 P) hb,
    subst_inVar (Formalism.L2.Th1.B.sgStar s2 P) 0 hb, subst_inVar (Formalism.L2.Th1.B.sgStar s2 P) 1 hb,
    subst_wpDiff P hb, hb0, hb1] at KE
  have sF := value_at hl0 hψ0 e hF0
  have sD := value_at hl0 hψ0 e hD0
  have s0 : PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K) (Formalism.L2.Th1.B.sgStar s2 P) =
      MvPowerSeries.X 0 * Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l)) :=
    value_at hl0 hψ0 e (U := MvPowerSeries.X 0) (by simp)
  have s1 : PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 1 l : MvPowerSeries (Fin 2) K) (Formalism.L2.Th1.B.sgStar s2 P) =
      MvPowerSeries.X 1 * Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l)) :=
    value_at hl0 hψ0 e (U := MvPowerSeries.X 1) (by simp)
  rw [← log_law hF, ← log_FI hF hi, sF, sD, s0, s1] at KE
  have C0 := curve_at (ι := Fin 2) hl0 h3 0
  have C1 := curve_at (ι := Fin 2) hl0 h3 1
  have hL0 := inVar_ne_zero hl1 0
  have hL1 := inVar_ne_zero hl1 1
  have hFne : F ≠ 0 := ne_zero_of_psubst hl0
    (by rw [log_law hF]; exact inVar_add_inVar_ne_zero hl1)
  have hDne : Formalism.L2.Th1.B.FI F i ≠ 0 := ne_zero_of_psubst hl0
    (by rw [log_FI hF hi]; exact inVar_sub_inVar_ne_zero hl1)
  have hN : (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K) ^ 2 * Formalism.InvariantFactorPaths.G7.at1 1 l ^ 2 * F * Formalism.L2.Th1.B.FI F i ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hL0) (pow_ne_zero 2 hL1)) hFne) hDne
  have hEE := addition_identity_products_eq_neg_c_mul_sq
    (L0 := (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K)) (L1 := Formalism.InvariantFactorPaths.G7.at1 1 l)
    (X0 := MvPowerSeries.X 0) (X1 := MvPowerSeries.X 1) (F := F) (D := Formalism.L2.Th1.B.FI F i) (c := c)
    (EF := Formalism.L2.Th1.B.fExp (-PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l)))
    (ED := Formalism.L2.Th1.B.fExp (-PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l)))
    (E0 := Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l)))
    (E1 := Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l)))
    (P0 := PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K) P)
    (P1 := PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 1 l : MvPowerSeries (Fin 2) K) P)
    (ep0 := Formalism.InvariantFactorPaths.G7.at1 0 ep) (ep1 := Formalism.InvariantFactorPaths.G7.at1 1 ep) (c0 := MvPowerSeries.C c0)
    hN (by linear_combination KE) (by linear_combination C0) (by linear_combination C1)
    (by linear_combination hc)
  have hA0 : MvPowerSeries.constantCoeff (PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hF0 _ hψ0
  have hB0 : MvPowerSeries.constantCoeff
      (PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hD0 _ hψ0
  have ha0 : MvPowerSeries.constantCoeff
      (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_inVar 0 hψ0
  have ha1 : MvPowerSeries.constantCoeff
      (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_inVar 1 hψ0
  have m0 := fExp_mul_neg ha0
  have m1 := fExp_mul_neg ha1
  have hc' : -c = Formalism.L2.Th1.B.fExp (-PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l)) *
      Formalism.L2.Th1.B.fExp (-PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l)) *
      Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 *
      Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 := by
    linear_combination
      (-(Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 *
        Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2)) * hEE +
      (c * (Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) *
          Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l)) + 1) *
        (Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) *
          Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l))) ^ 2) * m0 +
      (c * (Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) *
          Formalism.L2.Th1.B.fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l)) + 1)) * m1
  have hprod : Formalism.L2.Th1.B.fExp (-PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l)) *
      Formalism.L2.Th1.B.fExp (-PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l)) *
      Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 *
      Formalism.L2.Th1.B.fExp (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 =
      Formalism.L2.Th1.B.fExp (-PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l) +
        -PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l) +
        (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l)) +
        (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l))) := by
    rw [Formalism.L2.Th1.B.fExp_add, Formalism.L2.Th1.B.fExp_add, Formalism.L2.Th1.B.fExp_add, Formalism.L2.Th1.B.fExp_add, Formalism.L2.Th1.B.fExp_add]
    · ring
    all_goals simp [hA0, hB0, ha0, ha1]
  have hlog : Formalism.L2.Th1.B.fLog (-c) = -PowerSeries.subst F (Formalism.L2.Th1.B.phO s2 P l) +
        -PowerSeries.subst (Formalism.L2.Th1.B.FI F i) (Formalism.L2.Th1.B.phO s2 P l) +
        (Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.phO s2 P l)) +
        (Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.phO s2 P l)) := by
    rw [hc', hprod]
    exact Formalism.L2.Th1.B.fLog_fExp (by simp [hA0, hB0, ha0, ha1])
  rw [Formalism.L2.Th1.B.par, hlog]
  ring
end Formalism.L2.Th1.B.ParO
