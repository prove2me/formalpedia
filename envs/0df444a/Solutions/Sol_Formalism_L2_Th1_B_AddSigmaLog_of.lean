-- Prove2me | solution 1 for Formalism.L2.Th1.B.AddSigmaLog_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:11.956618+00:00
-- url     : https://prove2.me/submissions/6d56c21b-6688-4727-a95d-7d3fdcb49215

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_triple_lintegral_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add0_Lop_mulD
import Theorems.Thm_Formalism_L2_Th1_B_Add0_Lop_wpDiff
import Theorems.Thm_Formalism_L2_Th1_B_Add0_wpDiff_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add0_D_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_Add0_ne_zero_of_cc
import Theorems.Thm_Formalism_L2_Th1_B_Add0_Lop_log
import Theorems.Thm_Formalism_L2_Th1_B_Add0_evalYZero_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add0_evalFirst_X_one_mul_eq_zero
import Theorems.Thm_Formalism_L2_Th1_B_Add0_fLog_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1)
open Add0
namespace Formalism.L2.Th1.B
theorem _root_.solution (h2 : ExpLogDeriv) (h3 : ExpLogSubst) (h4 : PrimRules)
    (h5 : WaveUnique) (h6 : WaveKills) (h7 : ParCauchy) (h8 : WpReduced) (h9 : DqRule) :
    AddSigmaLog := by
  intro K _ _ g2 g3 P hP
  have hPodd := hP.2.1
  obtain ⟨f, hf⟩ : ∃ f, f = sigS P := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : MvPowerSeries (Fin 2) K,
      N = 1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P := ⟨_, rfl⟩
  rw [← hf, ← hNdef]
  have hN1 : MvPowerSeries.constantCoeff N = 1 := by simp [hNdef]
  have hNne : N ≠ 0 := ne_zero_of_cc hN1
  obtain ⟨hpr1, -⟩ := h4 K (prim P)
  obtain ⟨hpr1', -⟩ := h4 K P
  have hddf : dz (dz f) = -P := by
    rw [hf, sigS]
    show PowerSeries.derivative K (PowerSeries.derivative K (-prim (prim P))) = -P
    rw [map_neg, map_neg, show PowerSeries.derivative K (prim (prim P)) = prim P from hpr1,
      show PowerSeries.derivative K (prim P) = P from hpr1']
  have hLopN : Lop N = (2 * at1 0 P - 2 * at1 1 P) * N ^ 2 := by
    have e1 := Lop_wpDiff h8 hP
    rw [wpDiff_eq h9 hPodd, ← hNdef, Lop_mulD] at e1
    have hD2 : (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2 : MvPowerSeries (Fin 2) K) ^ 2 ≠ 0 :=
      pow_ne_zero _ D_ne_zero
    apply mul_left_cancel₀ hD2
    rw [e1]
    ring
  have hL : pd 0 (pd 0 (fLog N)) - pd 1 (pd 1 (fLog N)) = 2 * at1 0 P - 2 * at1 1 P := by
    have e2 := Lop_log h2 hN1
    rw [hLopN] at e2
    apply mul_left_cancel₀ (pow_ne_zero 2 hNne)
    rw [e2]
    ring
  have hW := h6 K f
  have hneg : ∀ x : Fin 2, (at1 x (-P) : MvPowerSeries (Fin 2) K) = -at1 x P := fun x => by
    rw [triple_lintegral_eq, map_neg, ← triple_lintegral_eq]
  rw [hddf, hneg, hneg] at hW
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [hf]
    simp only [sigS, map_neg, neg_eq_zero]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, prim, PowerSeries.coeff_mk, if_pos rfl]
  have hf1 : PowerSeries.coeff 1 f = 0 := by
    rw [hf]
    simp only [sigS, map_neg, prim, PowerSeries.coeff_mk, one_ne_zero, if_false, Nat.sub_self, if_true,
      zero_div, neg_zero]
  obtain ⟨hc0, hc1⟩ := h7 K f hf0 hf1
  have hφ : ∀ i, MvPowerSeries.constantCoeff (![(PowerSeries.X : PowerSeries K), 0] i) = 0 := by
    intro i
    fin_cases i
    · show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0
      exact PowerSeries.constantCoeff_X
    · simp
  have hevN : ev0 N = 1 := by
    rw [hNdef, show (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X 1 * (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 * dq P) by ring]
    rw [evalYZero_eq, map_sub, map_one, ← evalYZero_eq, evalFirst_X_one_mul_eq_zero, sub_zero]
  have hevL : ev0 (fLog N) = 0 := by
    have e4 := (h3 K (Fin 2) Unit ![(PowerSeries.X : PowerSeries K), 0] hφ).2 N hN1
    have e5 : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0] N = 1 := hevN
    unfold ev0
    rw [e4, e5, fLog_one]
  have hpdN : pd 1 N = MvPowerSeries.X 1 *
      (-(MvPowerSeries.X 0 ^ 2 * (2 * dq P + MvPowerSeries.X 1 * pd 1 (dq P)))) := by
    rw [hNdef]
    simp only [pd, map_sub, map_one, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) (by decide),
      Derivation.map_one_eq_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero, Nat.cast_ofNat,
      pow_one, Nat.add_one_sub_one]
    ring
  have hevpdL : ev0 (pd 1 (fLog N)) = 0 := by
    have e3 := (h2 K (Fin 2) 1).2 N hN1
    have e6 := congrArg ev0 e3
    rw [hpdN, evalFirst_X_one_mul_eq_zero, evalYZero_eq, map_mul, ← evalYZero_eq, ← evalYZero_eq, hevN, one_mul] at e6
    exact e6
  apply sub_eq_zero.1
  apply h5 K
  · simp only [map_sub]
    linear_combination hW - hL
  · rw [evalYZero_eq, map_sub, ← evalYZero_eq, ← evalYZero_eq, hc0, hevL, sub_zero]
  · rw [show pd 1 (par0 f - fLog N) = pd 1 (par0 f) - pd 1 (fLog N) from map_sub _ _ _, evalYZero_eq, map_sub,
      ← evalYZero_eq, ← evalYZero_eq, hc1, hevpdL, sub_zero]
end Formalism.L2.Th1.B
