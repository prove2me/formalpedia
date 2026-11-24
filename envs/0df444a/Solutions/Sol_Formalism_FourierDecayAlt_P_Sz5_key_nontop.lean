-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.key_nontop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:54.20621+00:00
-- url     : https://prove2.me/submissions/a9bedadb-75f5-46f0-971c-52682a9e2a9a

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_prod_Ioc_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_Icc_one_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_prodb_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_non_top_final_inequality
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vand_head
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_u_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_mu_bound

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
theorem _root_.solution (hNT : VandNonTop) (hEF : EdgeFactors) (c : Cfg) (bb : ℝ) (de : ℕ → ℝ) (h : c.Ok)
    (hs : c.Small bb) (hw : IsWord c.k de) (htop : c.top = false) :
    0 ≤ cOne c bb * c.prodb / c.aeff ∧
    (cOne c bb * c.prodb / c.aeff) ^ c.k * Vand c.k (c.u de) ≤
      Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) / 2 := by
  have hk4 := h.hk
  have hvthp : c.vthp = 0 := by simp [Cfg.vthp, htop]
  have haeff : c.aeff = c.a - c.v 1 := by simp [Cfg.aeff, htop]
  have hkR : (4:ℝ) ≤ (c.k:ℝ) := by exact_mod_cast hk4
  have hα : 1 ≤ c.a - c.v 1 := by
    have h1 := h.ha
    have h2 := h.hDel
    nlinarith
  have hcOne : cOne c bb * c.prodb / c.aeff =
      0.38 * Real.exp (-(2 * c.m * Real.log bb / c.k)) / (1 + 0) * c.prodb / (c.a - c.v 1) := by
    rw [haeff]
    unfold cOne
    rw [hvthp]
  rw [hcOne]
  have hB := prodb_ge_one c h
  obtain ⟨hVpos, hRde, hRlo, hRhi⟩ := hNT c de h hw htop
  obtain ⟨_, hEF2⟩ := hEF c de h hw
  obtain ⟨hPlo, hPhi⟩ := hEF2 htop
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
  have hexp : Real.exp ((c.k:ℝ) / 4) = Real.exp (1/4) ^ c.k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hP2 : Vand (c.k - 1) (fun i => c.u de (i + 1)) ≤ Real.exp (1/4) ^ c.k * Vand (c.k - 1) c.v := by
    rw [hRde, ← hexp]
    exact mul_le_mul_of_nonneg_right hRhi hVpos.le
  have hP20 : 0 ≤ Vand (c.k - 1) (fun i => c.u de (i + 1)) := by
    rw [hRde]
    exact mul_nonneg (le_trans (Real.exp_pos _).le hRlo) hVpos.le
  have hVu : Vand c.k (c.u de) ≤ (2 * (c.a - c.v 1)) ^ (c.k - 1) *
      (Real.exp (1/4) ^ c.k * Vand (c.k - 1) c.v) := by
    rw [hsplit]
    exact mul_le_mul hPhi hP2 hP20 (pow_nonneg (by linarith) _)
  constructor
  · exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  · exact non_top_final_inequality c.k (by omega) _ c.prodb (c.a - c.v 1) (Vand (c.k - 1) c.v)
      (Vand c.k (c.u de)) hα (Real.exp_pos _).le hB hVpos (mu_bound c h bb hs) hVu
end Formalism.FourierDecayAlt.P.Sz5
