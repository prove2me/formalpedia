-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.tWords_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:42.79253+00:00
-- url     : https://prove2.me/submissions/80a287f7-c412-451e-a3f9-975a7b459831

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_log_tp_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_sfac_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_one_word

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
theorem _root_.solution (hPA : PropA) (hEa : EaSize) (hVW : VandWords) : TWords := by
  intro ι _ G bb CDel Cb C0 Gam de de' T T' du du' hH hw hw' hT hT' hMR hLB hCC hCC' hds hC0 hGam
    hCh hCh' hf2 hC
  have hf : 2 ≤ Fintype.card ι := by
    have h1 : G.m ≤ G.f := hH.hmf
    have h2 : G.m = 2 * G.r + 2 := rfl
    have h3 : G.f = Fintype.card ι := rfl
    omega
  obtain ⟨w0⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hk : 4 ≤ G.k := (hH.hplace w0).hk
  have hkR : (4:ℝ) ≤ G.k := by exact_mod_cast hk
  have hfR : (2:ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hf
  have hV : ∀ w, 0 < Vand G.k ((G.place w).u de) ∧ 0 < Vand G.k ((G.place w).u de') ∧
      |Real.log (Vand G.k ((G.place w).u de') / Vand G.k ((G.place w).u de))| ≤ (G.k : ℝ) / 2 + 1 :=
    fun w => hVW (G.place w) de de' (hH.hplace w) (hH.hsmall w).hvth hw hw'
  have hkb : (4:ℝ) ≤ ((G.k : ℝ) * bb) ^ 8 := by
    have h1 : (4:ℝ) ≤ (G.k : ℝ) * bb := by
      have := hH.hbb
      nlinarith
    calc (4:ℝ) ≤ 4 ^ 8 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 8
  have hg1 : 4 ≤ G.g1 := by exact_mod_cast hkb.trans hH.hg1
  have hg2 : 4 ≤ G.g2 := by exact_mod_cast hkb.trans hH.hg2
  have hv0 : 0 < G.v := by have := hH.hv; linarith
  have hOk : (G.size de T du).Ok :=
    ⟨(by omega : 1 ≤ G.k), hv0, hH.hdF, (by omega : 2 ≤ G.g1), (by omega : 2 ≤ G.g2), hT, hH.hvol,
      fun w => (hV w).1⟩
  have hOk' : (G.size de' T' du').Ok :=
    ⟨(by omega : 1 ≤ G.k), hv0, hH.hdF, (by omega : 2 ≤ G.g1), (by omega : 2 ≤ G.g2), hT', hH.hvol,
      fun w => (hV w).2.1⟩
  have hX := one_word hPA hEa (G.size de T du) hOk hMR hLB hCC (by omega : 2 ≤ G.k) hg1 hg2 hds
    C0 Gam hC0 hGam hCh hf2
  have hX' := one_word hPA hEa (G.size de' T' du') hOk' hMR hLB hCC' (by omega : 2 ≤ G.k) hg1 hg2 hds
    C0 Gam hC0 hGam hCh' hf2
  have hdiff : ∀ w, Real.log ((G.size de T du).TcritPow w) - Real.log ((G.size de' T' du').TcritPow w)
      = Real.log (Vand G.k ((G.place w).u de') / Vand G.k ((G.place w).u de)) := by
    intro w
    have hg1' : (0:ℝ) < G.g1 := by exact_mod_cast (by omega : 0 < G.g1)
    have hg2' : (0:ℝ) < G.g2 := by exact_mod_cast (by omega : 0 < G.g2)
    exact log_tp_diff G.k (2 * G.r + 2) (Real.pi / G.v) (2 * G.v) ((G.g1 : ℝ) * (G.g2 : ℝ))
      (G.dsig w * (sfac (G.k + (2 * G.r + 2) - 1) : ℝ)) _ _
      (by have := Real.pi_pos; positivity) (by positivity) (by positivity)
      (by have := hds w; have := sfac_pos (G.k + (2 * G.r + 2) - 1); positivity) (hV w).1 (hV w).2.1
  have hsum : |∑ w, Real.log ((G.size de T du).TcritPow w) -
      ∑ w, Real.log ((G.size de' T' du').TcritPow w)| ≤ (Fintype.card ι : ℝ) * ((G.k : ℝ) / 2 + 1) := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ w, |Real.log ((G.size de T du).TcritPow w) -
          Real.log ((G.size de' T' du').TcritPow w)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : ι, ((G.k : ℝ) / 2 + 1) := by
          apply Finset.sum_le_sum; intro w _; rw [hdiff w]; exact (hV w).2.2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hC' : Real.log 2 + Real.log C0 ≤ (G.k : ℝ) * (Fintype.card ι : ℝ) / 16 := by
    have h2C : 0 < 2 * C0 := by linarith
    have h1 : (2 * C0) ^ (4 / ((G.k : ℝ) * (Fintype.card ι : ℝ))) ≤ Real.exp (1 / 4) := hC
    rw [Real.rpow_def_of_pos h2C, Real.exp_le_exp, Real.log_mul (by norm_num) (by linarith),
      mul_div_assoc', div_le_iff₀ (by positivity)] at h1
    linarith
  have hT0 : (0:ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hT0' : (0:ℝ) < T' := by exact_mod_cast (by omega : 0 < T')
  have hX1 : |(Fintype.card ι : ℝ) * ((G.k : ℝ) * Real.log T) -
      ∑ w, Real.log ((G.size de T du).TcritPow w) + 2 * Real.log Gam| ≤
      Real.log 2 + Real.log C0 := hX
  have hX1' : |(Fintype.card ι : ℝ) * ((G.k : ℝ) * Real.log T') -
      ∑ w, Real.log ((G.size de' T' du').TcritPow w) + 2 * Real.log Gam| ≤
      Real.log 2 + Real.log C0 := hX'
  rw [abs_le] at hX1 hX1' hsum
  have hfk : 0 < (Fintype.card ι : ℝ) * (G.k : ℝ) := by positivity
  have hf4 : (Fintype.card ι : ℝ) * 4 ≤ (Fintype.card ι : ℝ) * (G.k : ℝ) := by gcongr
  have hmain1 : (Fintype.card ι : ℝ) * (G.k : ℝ) * (Real.log T - Real.log T') ≤
      (Fintype.card ι : ℝ) * (G.k : ℝ) * 1 := by nlinarith [hX1.1, hX1.2, hX1'.1, hX1'.2, hsum.1, hsum.2]
  have hmain2 : (Fintype.card ι : ℝ) * (G.k : ℝ) * (-1) ≤
      (Fintype.card ι : ℝ) * (G.k : ℝ) * (Real.log T - Real.log T') := by
    nlinarith [hX1.1, hX1.2, hX1'.1, hX1'.2, hsum.1, hsum.2]
  have h1 := le_of_mul_le_mul_left hmain1 hfk
  have h2 := le_of_mul_le_mul_left hmain2 hfk
  have hTT : (T : ℝ) / T' = Real.exp (Real.log T - Real.log T') := by
    rw [Real.exp_sub, Real.exp_log hT0, Real.exp_log hT0']
  rw [hTT]
  exact ⟨Real.exp_le_exp.2 h2, Real.exp_le_exp.2 h1⟩
end Formalism.FourierDecayAlt.P.Sz5
