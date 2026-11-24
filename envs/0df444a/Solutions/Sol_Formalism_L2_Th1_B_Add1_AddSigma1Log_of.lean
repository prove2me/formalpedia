-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add1.AddSigma1Log_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:44:20.393829+00:00
-- url     : https://prove2.me/submissions/6102f68e-783c-48f9-8058-861999cf410b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
import Theorems.Thm_Formalism_L2_Th1_B_Add1_triple_lintegral_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add1_inVarAlgHom_C
import Theorems.Thm_Formalism_L2_Th1_B_Add1_evalYZero_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add1_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_B_Add1_restrictSecondZero_inVar_one
import Theorems.Thm_Formalism_L2_Th1_B_Add1_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_Add1_partialDeriv_inVar_of_ne
import Theorems.Thm_Formalism_L2_Th1_B_Add1_pd_mul
import Theorems.Thm_Formalism_L2_Th1_B_Add1_pd_sub
import Theorems.Thm_Formalism_L2_Th1_B_Add1_wave_alg
import Theorems.Thm_Formalism_L2_Th1_B_Add1_fLog_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
section SlopeTestRemainingChoices
variable {K : Type} [Field K] [CharZero K]
private theorem ev0_mul (a b : MvPowerSeries (Fin 2) K) :
    Formalism.L2.Th1.B.ev0 (a * b) = Formalism.L2.Th1.B.ev0 a * Formalism.L2.Th1.B.ev0 b := by
  simp only [evalYZero_eq, map_mul]
private theorem ev0_sub (a b : MvPowerSeries (Fin 2) K) :
    Formalism.L2.Th1.B.ev0 (a - b) = Formalism.L2.Th1.B.ev0 a - Formalism.L2.Th1.B.ev0 b := by
  simp only [evalYZero_eq, map_sub]
private theorem ev0_neg (a : MvPowerSeries (Fin 2) K) :
    Formalism.L2.Th1.B.ev0 (-a) = -Formalism.L2.Th1.B.ev0 a := by
  simp only [evalYZero_eq, map_neg]
private theorem ev0_one : Formalism.L2.Th1.B.ev0 (1 : MvPowerSeries (Fin 2) K) = 1 := by
  simp only [evalYZero_eq, map_one]
private theorem pd_neg {ι : Type} (i : ι) (x : MvPowerSeries ι K) :
    Formalism.L2.Th1.B.pd i (-x) = -Formalism.L2.Th1.B.pd i x :=
  map_neg (MvPowerSeries.pderiv K i) x
private theorem pd_one_eq_zero {ι : Type} (i : ι) : Formalism.L2.Th1.B.pd i (1 : MvPowerSeries ι K) = 0 :=
  MvPowerSeries.pderiv_one
private theorem pd_C_eq_zero {ι : Type} (i : ι) (c : K) :
    Formalism.L2.Th1.B.pd i (MvPowerSeries.C c : MvPowerSeries ι K) = 0 :=
  MvPowerSeries.pderiv_C
private theorem pd_zero_C_mul_at1_mul_at1 (c : K) (F G : PowerSeries K) :
    Formalism.L2.Th1.B.pd (0 : Fin 2) (MvPowerSeries.C c * Formalism.InvariantFactorPaths.G7.at1 0 F * Formalism.InvariantFactorPaths.G7.at1 1 G) =
      MvPowerSeries.C c * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz F) * Formalism.InvariantFactorPaths.G7.at1 1 G := by
  rw [pd_mul, pd_mul, partialDeriv_inVar_self,
    partialDeriv_inVar_of_ne (show (1 : Fin 2) ≠ 0 by decide), pd_C_eq_zero]
  ring
private theorem pd_one_C_mul_at1_mul_at1 (c : K) (F G : PowerSeries K) :
    Formalism.L2.Th1.B.pd (1 : Fin 2) (MvPowerSeries.C c * Formalism.InvariantFactorPaths.G7.at1 0 F * Formalism.InvariantFactorPaths.G7.at1 1 G) =
      MvPowerSeries.C c * Formalism.InvariantFactorPaths.G7.at1 0 F * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz G) := by
  rw [pd_mul, pd_mul, partialDeriv_inVar_self,
    partialDeriv_inVar_of_ne (show (0 : Fin 2) ≠ 1 by decide), pd_C_eq_zero]
  ring
private theorem pd_zero_one_sub_C_mul_at1_mul_at1 (kap : K) (w : PowerSeries K) :
    Formalism.L2.Th1.B.pd (0 : Fin 2) (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz w) * Formalism.InvariantFactorPaths.G7.at1 1 w) := by
  rw [pd_sub, pd_one_eq_zero, pd_zero_C_mul_at1_mul_at1]
  ring
private theorem pd_one_one_sub_C_mul_at1_mul_at1 (kap : K) (w : PowerSeries K) :
    Formalism.L2.Th1.B.pd (1 : Fin 2) (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz w)) := by
  rw [pd_sub, pd_one_eq_zero, pd_one_C_mul_at1_mul_at1]
  ring
private theorem pd_zero_pd_zero_one_sub_C_mul_at1_mul_at1 (kap : K) (w : PowerSeries K) :
    Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.pd (0 : Fin 2) (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w)) * Formalism.InvariantFactorPaths.G7.at1 1 w) := by
  rw [pd_zero_one_sub_C_mul_at1_mul_at1, pd_neg, pd_zero_C_mul_at1_mul_at1]
private theorem pd_one_pd_one_one_sub_C_mul_at1_mul_at1 (kap : K) (w : PowerSeries K) :
    Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.pd (1 : Fin 2) (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w))) := by
  rw [pd_one_one_sub_C_mul_at1_mul_at1, pd_neg, pd_one_C_mul_at1_mul_at1]
private theorem constantCoeff_one_sub_C_mul_at1_mul_at1 {kap : K} {w : PowerSeries K}
    (hw0 : PowerSeries.constantCoeff w = 0) :
    MvPowerSeries.constantCoeff ((1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) : MvPowerSeries (Fin 2) K) = 1 := by
  rw [map_sub, map_one, map_mul, map_mul, constantCoeff_inVar_eq_zero (0 : Fin 2) hw0]
  simp
private theorem constantCoeff_sig1S_eq_zero (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.constantCoeff (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Formalism.L2.Th1.B.sigmaOneSeries, Formalism.L2.Th1.B.prim]
private theorem coeff_one_sig1S_eq_zero (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.coeff 1 (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w) = 0 := by
  simp [Formalism.L2.Th1.B.sigmaOneSeries, Formalism.L2.Th1.B.prim]
private theorem dz_dz_sig1S_eq_neg_C_add_C_mul (h4 : Formalism.L2.Th1.B.PrimRules) (e1 kap : K) (w : PowerSeries K) :
    Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w)) = -(PowerSeries.C e1 + PowerSeries.C kap * w) := by
  have hp : ∀ f : PowerSeries K, PowerSeries.derivative K (Formalism.L2.Th1.B.prim f) = f := fun f => (h4 K f).1
  show PowerSeries.derivative K (PowerSeries.derivative K
      (-Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (PowerSeries.C e1 + PowerSeries.C kap * w)))) = _
  rw [Derivation.map_neg, Derivation.map_neg, hp, hp]
private theorem at1_neg_C_add_C_mul {ι : Type} (e1 kap : K) (w : PowerSeries K) (x : ι) :
    Formalism.InvariantFactorPaths.G7.at1 x (-(PowerSeries.C e1 + PowerSeries.C kap * w)) =
      -(MvPowerSeries.C e1 + MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 x w) := by
  simp only [triple_lintegral_eq, map_neg, map_add, map_mul, inVarAlgHom_C]
private theorem at1_dz_sq_eq_cubic {A kap : K} {w : PowerSeries K}
    (hw : Formalism.L2.Th1.B.dz w ^ 2 = 4 * w + 4 * PowerSeries.C A * w ^ 2 + 4 * PowerSeries.C kap * w ^ 3)
    (x : Fin 2) :
    Formalism.InvariantFactorPaths.G7.at1 x (Formalism.L2.Th1.B.dz w) ^ 2 = 4 * Formalism.InvariantFactorPaths.G7.at1 x w + 4 * MvPowerSeries.C A * Formalism.InvariantFactorPaths.G7.at1 x w ^ 2 +
      4 * MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 x w ^ 3 := by
  have h := congrArg (at1H (K := K) x) hw
  simp only [map_add, map_mul, map_pow, map_ofNat, inVarAlgHom_C] at h
  simp only [triple_lintegral_eq]
  exact h
private theorem at1_dz_dz_eq_quadratic {A kap : K} {w : PowerSeries K}
    (hw : Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w) = 2 + 4 * PowerSeries.C A * w + 6 * PowerSeries.C kap * w ^ 2)
    (x : Fin 2) :
    Formalism.InvariantFactorPaths.G7.at1 x (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w)) = 2 + 4 * MvPowerSeries.C A * Formalism.InvariantFactorPaths.G7.at1 x w +
      6 * MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 x w ^ 2 := by
  rw [hw]
  simp only [triple_lintegral_eq, map_add, map_mul, map_pow, map_ofNat, inVarAlgHom_C]
end SlopeTestRemainingChoices
end Formalism.L2.Th1.B.Add1
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
set_option maxHeartbeats 800000
namespace Formalism.L2.Th1.B.Add1
theorem _root_.solution (h1 : ExpLogRules) (h2 : ExpLogDeriv) (h3 : ExpLogSubst) (h4 : PrimRules)
    (h5 : WaveUnique) (h6 : WaveKills) (h7 : ParCauchy) (h8 : WSecond) : AddSigma1Log := by
  unfold Formalism.L2.Th1.B.AddSigma1Log
  intro K _ _ A kap e1 w hw
  have hw0 : PowerSeries.constantCoeff w = 0 := hw.1
  obtain ⟨hw1, hw2⟩ := h8 K A kap w hw
  have hwd0 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.dz w) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp [hw1]
  have hL0 := constantCoeff_sig1S_eq_zero e1 kap w
  have hL1 := coeff_one_sig1S_eq_zero e1 kap w
  have hL2 := dz_dz_sig1S_eq_neg_C_add_C_mul h4 e1 kap w
  obtain ⟨hC0, hC1⟩ := h7 K _ hL0 hL1
  have hg : MvPowerSeries.constantCoeff ((1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) : MvPowerSeries (Fin 2) K) = 1 :=
    constantCoeff_one_sub_C_mul_at1_mul_at1 hw0
  have hW : Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.par0 (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w))) -
      Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.par0 (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w))) =
      2 * MvPowerSeries.C kap * (Formalism.InvariantFactorPaths.G7.at1 0 w - Formalism.InvariantFactorPaths.G7.at1 1 w) := by
    rw [h6 K, hL2, at1_neg_C_add_C_mul, at1_neg_C_add_C_mul]
    ring
  have hd0 := (h2 K (Fin 2) 0).2 _ hg
  have hd1 := (h2 K (Fin 2) 1).2 _ hg
  have e0 : (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) * Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz w) * Formalism.InvariantFactorPaths.G7.at1 1 w) :=
    hd0.trans (pd_zero_one_sub_C_mul_at1_mul_at1 kap w)
  have e1' : (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) * Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz w)) :=
    hd1.trans (pd_one_one_sub_C_mul_at1_mul_at1 kap w)
  have f0 : -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz w) * Formalism.InvariantFactorPaths.G7.at1 1 w) *
        Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) +
      (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) * Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.pd (0 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w))) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w)) * Formalism.InvariantFactorPaths.G7.at1 1 w) := by
    have t := congrArg (Formalism.L2.Th1.B.pd (0 : Fin 2)) hd0
    rw [pd_mul, pd_zero_pd_zero_one_sub_C_mul_at1_mul_at1, pd_zero_one_sub_C_mul_at1_mul_at1] at t
    linear_combination t
  have f1 : -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz w)) *
        Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) +
      (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) * Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w))) =
      -(MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 (Formalism.L2.Th1.B.dz (Formalism.L2.Th1.B.dz w))) := by
    have t := congrArg (Formalism.L2.Th1.B.pd (1 : Fin 2)) hd1
    rw [pd_mul, pd_one_pd_one_one_sub_C_mul_at1_mul_at1, pd_one_one_sub_C_mul_at1_mul_at1] at t
    linear_combination t
  have hsq := wave_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW e0 f0 e1' f1
    (at1_dz_sq_eq_cubic hw.2.2 0) (at1_dz_sq_eq_cubic hw.2.2 1)
    (at1_dz_dz_eq_quadratic hw2 0) (at1_dz_dz_eq_quadratic hw2 1)
  have hu : IsUnit (((1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) : MvPowerSeries (Fin 2) K) ^ 2) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [map_pow, hg, one_pow]; exact isUnit_one)
  have hwave := hu.mul_left_cancel hsq
  have hRg : Formalism.L2.Th1.B.ev0 ((1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) : MvPowerSeries (Fin 2) K) = 1 := by
    rw [ev0_sub, ev0_one, ev0_mul, restrictSecondZero_inVar_one hw0, mul_zero, sub_zero]
  have hRl : Formalism.L2.Th1.B.ev0 (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) = 0 := by
    have hφ : ∀ i, MvPowerSeries.constantCoeff
        ((![(PowerSeries.X : PowerSeries K), 0] : Fin 2 → PowerSeries K) i) = 0 := by
      intro i; fin_cases i
      · exact PowerSeries.constantCoeff_X
      · exact map_zero _
    have e : Formalism.L2.Th1.B.ev0 (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) = Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.ev0 ((1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w) : MvPowerSeries (Fin 2) K)) :=
      (h3 K (Fin 2) Unit ![(PowerSeries.X : PowerSeries K), 0] hφ).2 _ hg
    rw [e, hRg]
    exact fLog_one h1
  have hRp : Formalism.L2.Th1.B.ev0 (Formalism.L2.Th1.B.pd (1 : Fin 2) (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w))) = 0 := by
    have t := congrArg Formalism.L2.Th1.B.ev0 hd1
    rw [ev0_mul, hRg, one_mul, pd_one_one_sub_C_mul_at1_mul_at1, ev0_neg, ev0_mul,
      restrictSecondZero_inVar_one hwd0, mul_zero, neg_zero] at t
    exact t
  have hfin : (Formalism.L2.Th1.B.par0 (Formalism.L2.Th1.B.sigmaOneSeries e1 kap w)) - (Formalism.L2.Th1.B.fLog (1 - MvPowerSeries.C kap * Formalism.InvariantFactorPaths.G7.at1 0 w * Formalism.InvariantFactorPaths.G7.at1 1 w)) = 0 := by
    apply h5 K
    · simp only [pd_sub]
      exact hwave
    · rw [ev0_sub, hC0, hRl, sub_zero]
    · rw [pd_sub, ev0_sub, hC1, hRp, sub_zero]
  exact sub_eq_zero.mp hfin
end Formalism.L2.Th1.B.Add1
