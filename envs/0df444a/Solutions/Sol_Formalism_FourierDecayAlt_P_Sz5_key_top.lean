-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.key_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:42.765996+00:00
-- url     : https://prove2.me/submissions/679ccdac-8e68-45cd-9b0c-a292f4df7177

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_prod_Ioc_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_Icc_one_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_v_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_prodb_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_top_final_inequality
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vand_head
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vand_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_u_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_u_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_u_mid_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_mu_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_last


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (hTp : VandTop) (c : Cfg) (bb : ℝ) (de : ℕ → ℝ) (h : c.Ok)
    (hs : c.Small bb) (hw : IsWord c.k de) (htop : c.top = true) :
    0 ≤ cOne c bb * c.prodb / c.aeff ∧
    (cOne c bb * c.prodb / c.aeff) ^ c.k * Vand c.k (c.u de) ≤
      Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) / 2 := by
  have hk4 := h.hk
  have hkR : (4:ℝ) ≤ (c.k:ℝ) := by exact_mod_cast hk4
  have hD := h.hDel
  have hD0 : 0 < c.Del := by linarith
  obtain ⟨hbp1, hbp2⟩ := h.htop htop
  have hb1 := h.hb1
  have hbp0 : 3 ≤ c.bp := by linarith
  have hbpne : c.bp ≠ 0 := (by linarith : (0:ℝ) < c.bp).ne'
  have hvthp : c.vthp = 4 * c.k * c.Del / c.bp := by simp [Cfg.vthp, htop]
  have haeff : c.aeff = c.a * c.bp / (c.k * c.Del) := by simp [Cfg.aeff, htop]
  have hv1 := h.hv1
  have hv1n : 0 ≤ c.v 1 := v_nonneg c h 1 (by omega)
  have ha := h.ha
  have hK0 : 0 < (c.k:ℝ) * c.Del := by positivity
  have ha0 : 0 < c.a := by linarith
  have hθ : 1 ≤ 1 + 4 * (c.k:ℝ) * c.Del / c.bp := by
    have h4 : 0 ≤ 4 * (c.k:ℝ) * c.Del / c.bp := by positivity
    linarith
  have hcOne : cOne c bb * c.prodb / c.aeff =
      0.38 * Real.exp (-(2 * c.m * Real.log bb / c.k)) / (1 + 4 * c.k * c.Del / c.bp) * c.prodb /
        (c.a * c.bp / (c.k * c.Del)) := by
    rw [haeff]
    unfold cOne
    rw [hvthp]
  rw [hcOne]
  have hB := prodb_ge_one c h
  obtain ⟨hW, hRde, hRlo, hRhi, hV1⟩ := hTp c de h hw
  have hvth := hs.hvth
  unfold Cfg.vth at hvth
  have hb1pos : 0 < c.b 1 := by linarith
  have hvth' : 4 * (c.m:ℝ) * c.k * c.Del ≤ c.b 1 / 10 := by
    first
    | (rw [div_le_iff₀ hb1pos] at hvth; linarith)
    | (rw [div_le_iff hb1pos] at hvth; linarith)
  have hm2 : (2:ℝ) ≤ (c.m:ℝ) := by exact_mod_cast h.hm
  have hK1 : (c.k:ℝ) * c.Del ≤ c.bp / 40 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm2) hK0.le]
  have hK2 : (c.k:ℝ) * c.Del ≤ c.a / 4 := by linarith
  have hK4 : (4:ℝ) ≤ (c.k:ℝ) * c.Del := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (sub_nonneg.mpr hD)]
  have hq : ((c.k:ℝ) * c.Del) ^ 2 * (c.a + c.bp) ≤ c.a ^ 2 * c.bp ^ 2 := by
    have s1 := mul_le_mul_of_nonneg_right (mul_self_le_mul_self hK0.le hK1) ha0.le
    have s3 := mul_le_mul_of_nonneg_right (mul_self_le_mul_self hK0.le hK2)
      (by linarith : (0:ℝ) ≤ c.bp)
    have s2 : 0 ≤ c.bp ^ 2 * c.a * (c.a / 2 - 1 / 1600) := by
      apply mul_nonneg (mul_nonneg (sq_nonneg _) ha0.le)
      linarith
    have s4 : 0 ≤ c.a ^ 2 * c.bp * (c.bp / 2 - 1 / 16) := by
      apply mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith))
      linarith
    nlinarith
  have hsplit : Vand c.k (c.u de) =
      (∏ i ∈ Icc 2 c.k, (c.a - c.u de i)) * Vand (c.k - 1) (fun i => c.u de (i + 1)) := by
    have hk1 : c.k = (c.k - 1) + 1 := by omega
    conv_lhs => rw [hk1]
    rw [vand_head, u_one]
    congr 1
    have hI : Icc 2 c.k = Ioc 1 c.k := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      constructor <;> intro hh <;> exact ⟨by omega, by omega⟩
    have hs2 := prod_Ioc_shift (fun i => c.a - c.u de i) 1 0 (c.k - 1)
    rw [zero_add, show c.k - 1 + 1 = c.k by omega] at hs2
    rw [Icc_one_eq, hI]
    exact hs2.symm
  have hulast : c.u de c.k = -c.bp := by
    rw [u_last c de hk4]
    simp [Cfg.ulast, htop]
  have hP1 : ∏ i ∈ Icc 2 c.k, (c.a - c.u de i) =
      (∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i)) * (c.a + c.bp) := by
    have hI : Icc 2 c.k = Ioc 1 c.k := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      constructor <;> intro hh <;> exact ⟨by omega, by omega⟩
    rw [hI]
    have hk1 : c.k = (c.k - 1) + 1 := by omega
    conv_lhs => rw [hk1]
    rw [Finset.prod_Ioc_succ_top (by omega : 1 ≤ c.k - 1), ← hk1, hulast]
    ring
  have hA1 : ∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i) ≤ c.a ^ (c.k - 2) := by
    calc ∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i) ≤ ∏ i ∈ Ioc 1 (c.k - 1), c.a := by
          apply Finset.prod_le_prod
          · intro i hi
            rw [Finset.mem_Ioc] at hi
            obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            have hb := u_mid_bounds c h de hw j (by omega) (by omega)
            linarith [hb.2]
          · intro i hi
            rw [Finset.mem_Ioc] at hi
            obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            have hb := u_mid_bounds c h de hw j (by omega) (by omega)
            linarith [hb.1]
      _ = c.a ^ (c.k - 2) := by
          first
          | (rw [Finset.prod_const, Nat.card_Ioc]; done)
          | (rw [Finset.prod_const, Nat.card_Ioc, Nat.sub_sub])
          | (rw [Finset.prod_const, Nat.card_Ioc]; congr 1; omega)
  have hA10 : 0 ≤ ∏ i ∈ Ioc 1 (c.k - 1), (c.a - c.u de i) := by
    apply Finset.prod_nonneg
    intro i hi
    rw [Finset.mem_Ioc] at hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hb := u_mid_bounds c h de hw j (by omega) (by omega)
    linarith [hb.2]
  have hP2split : Vand (c.k - 1) (fun i => c.u de (i + 1)) =
      Vand (c.k - 2) (fun i => c.u de (i + 1)) * ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp) := by
    have hk2 : c.k - 1 = (c.k - 2) + 1 := by omega
    rw [hk2, vand_last]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    try beta_reduce
    rw [show c.k - 2 + 1 + 1 = c.k by omega, hulast]
    ring
  have hF : ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp) ≤
      (c.bp * (1 + 4 * c.k * c.Del / c.bp)) ^ (c.k - 2) := by
    have hbt : c.bp * (1 + 4 * c.k * c.Del / c.bp) = c.bp + 4 * c.k * c.Del := by
      have e : c.bp * c.bp⁻¹ = 1 := mul_inv_cancel₀ hbpne
      linear_combination (4 * (c.k:ℝ) * c.Del) * e
    rw [hbt]
    calc ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp)
        ≤ ∏ i ∈ Icc 1 (c.k - 2), (c.bp + 4 * (c.k:ℝ) * c.Del) := by
          apply Finset.prod_le_prod
          · intro i hi
            rw [Finset.mem_Icc] at hi
            have hb := u_mid_bounds c h de hw i hi.1 (by omega)
            linarith [hb.1]
          · intro i hi
            rw [Finset.mem_Icc] at hi
            have hb := u_mid_bounds c h de hw i hi.1 (by omega)
            linarith [hb.2]
      _ = (c.bp + 4 * (c.k:ℝ) * c.Del) ^ (c.k - 2) := by
          rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hF0 : 0 ≤ ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) + c.bp) := by
    apply Finset.prod_nonneg
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hb := u_mid_bounds c h de hw i hi.1 (by omega)
    linarith [hb.1]
  have hexp : Real.exp (((c.k:ℝ) - 1) / 4) = Real.exp (1/4) ^ (c.k - 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [Nat.cast_sub (show 1 ≤ c.k by omega), Nat.cast_one]
    ring
  have hV2 : Vand (c.k - 2) (fun i => c.u de (i + 1)) ≤ Real.exp (1/4) ^ (c.k - 1) * Vand (c.k - 2) c.v := by
    rw [hRde, ← hexp]
    exact mul_le_mul_of_nonneg_right hRhi hW.le
  have hV20 : 0 ≤ Vand (c.k - 2) (fun i => c.u de (i + 1)) := by
    rw [hRde]
    exact mul_nonneg (le_trans (Real.exp_pos _).le hRlo) hW.le
  have hab : 0 ≤ c.a + c.bp := by linarith
  have hVu : Vand c.k (c.u de) ≤ (c.a ^ (c.k - 2) * (c.a + c.bp)) *
      ((Real.exp (1/4) ^ (c.k - 1) * Vand (c.k - 2) c.v) *
        (c.bp * (1 + 4 * c.k * c.Del / c.bp)) ^ (c.k - 2)) := by
    rw [hsplit, hP1, hP2split]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hA1 hab)
      (mul_le_mul hV2 hF hF0 (mul_nonneg (by positivity) hW.le))
      (mul_nonneg hV20 hF0) (mul_nonneg (pow_nonneg ha0.le _) hab)
  rw [hV1]
  constructor
  · have hX : 0 ≤ 0.38 * Real.exp (-(2 * c.m * Real.log bb / c.k)) / (1 + 4 * c.k * c.Del / c.bp) := by
      positivity
    exact div_nonneg (mul_nonneg hX (by linarith)) (by positivity)
  · exact top_final_inequality c.k hk4 _ c.prodb c.a c.bp c.Del _ (Vand (c.k - 2) c.v) (Vand c.k (c.u de))
      (Real.exp_pos _).le hB hW (mu_bound c h bb hs) hθ ha0 (by linarith) hD0 hq hVu
end Formalism.FourierDecayAlt.P.Sz5
