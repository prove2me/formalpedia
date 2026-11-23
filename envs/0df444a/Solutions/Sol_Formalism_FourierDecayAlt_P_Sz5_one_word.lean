-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.one_word
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:18.155654+00:00
-- url     : https://prove2.me/submissions/5b24c9a4-627d-401d-8844-a30a925b7d6b

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_tcritPow_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_sfac_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_colIdx_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_tcritPow_pos


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
theorem _root_.solution (hPA : PropA) (hEa : EaSize) {ι : Type} [Fintype ι] (S : SizeData ι) (hOk : S.Ok)
    (hMR : S.MassRatios) (hLB : S.LBound) (hCC : S.ColumnCount) (hk : 2 ≤ S.k) (hg1 : 4 ≤ S.g1)
    (hg2 : 4 ≤ S.g2) (hds : ∀ w, 0 < S.dsig w) (C0 Gam : ℝ) (hC0 : 1 ≤ C0) (hGam : 0 < Gam)
    (hCh : S.ChoiceOfT C0 Gam) (hf2 : (S.f : ℝ) * (8 / 2 ^ S.k) ≤ Real.log 2) :
    |(S.f : ℝ) * ((S.k : ℝ) * Real.log S.T) - ∑ w, Real.log (S.TcritPow w) + 2 * Real.log Gam| ≤
      Real.log 2 + Real.log C0 := by
  have hk1 := hOk.hk
  have hv0 := hOk.hv
  have hT2 := hOk.hT
  have hg1' : (1:ℝ) < (S.g1:ℝ) := by exact_mod_cast (by omega : 1 < S.g1)
  have hg2' : (1:ℝ) < (S.g2:ℝ) := by exact_mod_cast (by omega : 1 < S.g2)
  have hTk2 : 2 ≤ S.T ^ S.k := le_trans hT2 (Nat.le_self_pow (by omega) _)
  have hTkR : (2:ℝ) ≤ (S.T:ℝ) ^ S.k := by exact_mod_cast hTk2
  have hTk : (0:ℝ) < (S.T:ℝ) ^ S.k := by linarith
  have hdu : 0 < S.du := by
    have hCC' := hCC
    unfold SizeData.ColumnCount at hCC'
    rw [hCC']
    have h1 : 0 < S.idxCol := by
      unfold SizeData.idxCol
      exact mul_pos (pow_pos (colIdx_pos S.k _ hg1') _) (pow_pos (colIdx_pos S.k _ hg2') _)
    have h2 : 0 < ∏ w, S.dimPi w := by
      apply Finset.prod_pos
      intro w _
      unfold SizeData.dimPi
      exact div_pos (hOk.hVu w) (sfac_pos _)
    have h4 : 0 < ((S.T:ℝ) ^ S.k - 1) ^ S.f := pow_pos (by linarith) _
    exact mul_pos (mul_pos (mul_pos hOk.hvol h1) h2) h4
  obtain ⟨hEa0, hEa2⟩ := hEa ι S hOk hLB hk hg1 hg2
  have hka : 0 < S.ka := by
    unfold SizeData.ka
    positivity
  have hrd : 0 < S.rd := by
    unfold SizeData.rd
    positivity
  have hg : 0 < S.g := by
    unfold SizeData.g
    exact mul_pos (by linarith) (by linarith)
  have hTc : ∀ w, 0 < S.TcritPow w := by
    intro w
    unfold SizeData.TcritPow
    have hVV : 0 < S.VV w := by
      unfold SizeData.VV
      exact mul_pos (hds w) (sfac_pos _)
    exact tcritPow_pos _ _ _ _ _ _ _ hka hrd hg hVV (hOk.hVu w)
  have hPA' := hPA ι S hOk hMR hCC
  have hprod : 0 < ∏ w, (S.TcritPow w / (S.T:ℝ) ^ S.k) :=
    Finset.prod_pos (fun w _ => div_pos (hTc w) hTk)
  have hR : 0 < S.Dstar / S.du := by
    rw [hPA']
    exact mul_pos hEa0 hprod
  have hDs : 0 < S.Dstar := by
    first
    | exact (div_pos_iff_of_pos_right hdu).mp hR
    | (have h5 := mul_pos hR hdu
       rwa [div_mul_cancel₀ _ hdu.ne'] at h5)
  have hlog : Real.log (S.Dstar / S.du) =
      Real.log S.Ea + ∑ w, (Real.log (S.TcritPow w) - S.k * Real.log S.T) := by
    have hlp : Real.log (∏ w, (S.TcritPow w / (S.T:ℝ) ^ S.k)) =
        ∑ w, Real.log (S.TcritPow w / (S.T:ℝ) ^ S.k) := by
      first
      | exact Real.log_prod (fun w _ => (div_pos (hTc w) hTk).ne')
      | exact Real.log_prod _ _ (fun w _ => (div_pos (hTc w) hTk).ne')
    rw [hPA', Real.log_mul hEa0.ne' hprod.ne', hlp]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    rw [Real.log_div (hTc w).ne' hTk.ne', Real.log_pow]
  have hsum : ∑ w, (Real.log (S.TcritPow w) - S.k * Real.log S.T) =
      ∑ w, Real.log (S.TcritPow w) - (S.f:ℝ) * (S.k * Real.log S.T) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    try rfl
  have eL : Real.log (S.Dstar / S.du) = Real.log S.Dstar - Real.log S.du :=
    Real.log_div hDs.ne' hdu.ne'
  obtain ⟨hc1, hc2⟩ := hCh
  have hC00 : 0 < C0 := by linarith
  have hl1 := Real.log_le_log (by positivity) hc1
  have hl2 := Real.log_le_log hdu hc2
  have eA : Real.log ((Gam ^ 2)⁻¹ * S.Dstar * C0⁻¹) =
      -(2 * Real.log Gam) + Real.log S.Dstar - Real.log C0 := by
    rw [Real.log_mul (by positivity : (Gam ^ 2)⁻¹ * S.Dstar ≠ 0) (by positivity : C0⁻¹ ≠ 0),
      Real.log_mul (by positivity : (Gam ^ 2)⁻¹ ≠ 0) hDs.ne', Real.log_inv, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have eB : Real.log ((Gam ^ 2)⁻¹ * S.Dstar * C0) =
      -(2 * Real.log Gam) + Real.log S.Dstar + Real.log C0 := by
    rw [Real.log_mul (by positivity : (Gam ^ 2)⁻¹ * S.Dstar ≠ 0) hC00.ne',
      Real.log_mul (by positivity : (Gam ^ 2)⁻¹ ≠ 0) hDs.ne', Real.log_inv, Real.log_pow]
    push_cast
    ring
  rw [eA] at hl1
  rw [eB] at hl2
  have hE := abs_le.mp hEa2
  rw [abs_le]
  constructor <;> linarith [hE.1, hE.2]
end Formalism.FourierDecayAlt.P.Sz5
