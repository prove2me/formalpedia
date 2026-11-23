-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChainAndRowSums.rowSums_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:01.846573+00:00
-- url     : https://prove2.me/submissions/62c2d694-0568-457b-8c8f-8ea447e2b6e0

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainAndRowSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_cm_two
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_cm_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_cm_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChainAndRowSums
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.ChainAndRowSums
theorem _root_.solution : RowSums := by
  intro W Wd s c caa M Maa hs hc hcaa hM hMaa
  have row : ∀ n, 1 ≤ n → n < s → ∀ w ∈ Wd,
      ∑ w'' ∈ Wd, chainMat Wd c n w w'' = ∏ k ∈ Ico 1 (n + 1), M k := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ m ih =>
      intro _ hns w hw
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [cm_one, hM 1 le_rfl hns w hw]
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [show k + 1 + 1 = k + 2 from rfl]
        simp only [cm_two]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun w' hw' => by rw [ih (by omega) (by omega) w' hw'])]
        rw [← Finset.sum_mul, hM (k + 2) (by omega) hns w hw,
          Finset.prod_Ico_succ_top (a := 1) (b := k + 2) (by omega), mul_comm]
  have P := fun w hw => row (s - 1) (by omega) (by omega) w hw
  have hs1 : s - 1 + 1 = s := by omega
  rw [hs1] at P
  have rsum : ∀ w ∈ Wd, ∑ w'' ∈ Wd, coMat Wd c caa s w w'' = Maa * ∏ n ∈ Ico 1 s, M n := by
    intro w hw
    simp only [coMat]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun w' hw' => by rw [P w' hw']), ← Finset.sum_mul, hMaa w hw]
  intro w hw
  refine ⟨rsum w hw, fun hpos => ⟨fun a => ?_, fun a ha => by simp [ha], ?_⟩⟩
  · dsimp only
    split_ifs
    · exact div_nonneg (Finset.sum_nonneg (fun x _ => mul_nonneg (hcaa _ _)
        (cm_nonneg Wd c hc _ _ _))) hpos.le
    · exact le_rfl
  · rw [Finset.sum_congr rfl (fun a ha => if_pos ha), ← Finset.sum_div, rsum w hw]
    exact div_self hpos.ne'
end Formalism.FourierDecayAlt.P.ChainAndRowSums
