-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.corA_of_propA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:07.801017+00:00
-- url     : https://prove2.me/submissions/8e77e6a1-49c6-4b43-934e-505ce0a9413e

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_eaSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_ratio_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_root_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_tcritPow_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution (hPA : PropA) : CorA := by
  intro ι _ S C0 CG C' L hOk hMR hLB hCC hds hk hg1 hg2 hC0 hCG hL hC' hkb hf2 hCh
  obtain ⟨hEa, hEa'⟩ := eaSize ι S hOk hLB hk hg1 hg2
  have hPA' := hPA ι S hOk hMR hCC
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = CG * (S.m : ℝ) ^ 5 * S.f * L := ⟨_, rfl⟩
  rw [← hX] at hCh
  have hk1 : 1 ≤ S.k := hOk.hk
  have hkne : S.k ≠ 0 := by omega
  have hT0 : (0 : ℝ) < S.T := by
    have := hOk.hT
    exact_mod_cast (by omega : 0 < S.T)
  have hmfL : 0 ≤ (S.m : ℝ) ^ 5 * S.f * L := by positivity
  have hX0 : 0 ≤ X := by
    have := mul_nonneg hCG hmfL
    rw [hX]
    linarith
  have hX8 : 8 * X ≤ S.k := by
    have h1 : 8 * CG * ((S.m : ℝ) ^ 5 * S.f * L) ≤ C' * ((S.m : ℝ) ^ 5 * S.f * L) :=
      mul_le_mul_of_nonneg_right hC' hmfL
    rw [hX]
    linarith
  have hTP : ∀ w, 0 < S.TcritPow w := tcritPow_pos S hOk hds
  have hTc0 : ∀ w, 0 < S.Tcrit w := by
    intro w
    exact Real.rpow_pos_of_pos (hTP w) _
  have hTc : ∀ w, S.Tcrit w ^ S.k = S.TcritPow w := by
    intro w
    have : S.Tcrit w = (S.TcritPow w) ^ ((S.k : ℝ)⁻¹) := by
      unfold SizeData.Tcrit Sz.Tcrit SizeData.TcritPow
      rw [one_div]
    rw [this, Real.rpow_inv_natCast_pow (hTP w).le hkne]
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∏ w, (S.Tcrit w / S.T) := ⟨_, rfl⟩
  rw [← hP]
  have hP0 : 0 < P := by
    rw [hP]
    exact Finset.prod_pos (fun w _ => div_pos (hTc0 w) hT0)
  have hPk : P ^ S.k = ∏ w, (S.TcritPow w / (S.T : ℝ) ^ S.k) := by
    rw [hP, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro w _
    rw [div_pow, hTc]
  rw [← hPk] at hPA'
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = S.Dstar / S.du := ⟨_, rfl⟩
  rw [← hR] at hPA'
  have hR0 : 0 < R := by rw [hPA']; positivity
  have hdu : S.du ≠ 0 := by
    intro h
    rw [h, div_zero] at hR
    linarith
  have hD : S.Dstar = R * S.du := by rw [hR, div_mul_cancel₀ _ hdu]
  have hG2e : Real.exp X ^ 2 = Real.exp (2 * X) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hRb : Real.exp (2 * X) / C0 ≤ R ∧ R ≤ Real.exp (2 * X) * C0 := by
    obtain ⟨c1, c2⟩ := hCh
    rw [hG2e, hD] at c1 c2
    exact ratio_bounds (Real.exp_pos _) hC0 hdu c1 c2
  have hEab := abs_le.mp (hEa'.trans hf2)
  have hEa2 : S.Ea ≤ 2 := (Real.log_le_log_iff hEa (by norm_num)).mp hEab.2
  have hEa12 : 1 / 2 ≤ S.Ea := by
    have : Real.log (1 / 2) ≤ Real.log S.Ea := by
      rw [one_div, Real.log_inv]; exact hEab.1
    exact (Real.log_le_log_iff (by norm_num) hEa).mp this
  rw [hPA'] at hRb
  exact root_bounds hP0 hk1 hC0 hX0 hX8 hEa12 hEa2 hRb.1 hRb.2
end Formalism.FourierDecayAlt.P.Sz2
