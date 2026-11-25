-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.density_ordinary_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:42:50.819249+00:00
-- url     : https://prove2.me/submissions/5c3d570b-82d6-4bc8-8e82-8666d6a8143c

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_geom_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_le_exp
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_inv_le_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.DensOrdinaryBound := by
  intro η q k r c l l' hη hq hk hc hl hl'
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set n : ℤ := ((k + 2 * r + 1 : ℕ) : ℤ) with hn
  have hnk : n = (k : ℤ) + 2 * r + 1 := by rw [hn]; push_cast; ring
  rcases le_or_gt ((k : ℤ) - c) 0 with h0 | h0
  · rw [densityProduct_eq_zero η q _ _ h0 (by omega), zero_div]
    exact (Real.exp_pos _).le
  · have hlk : (k : ℤ) ≤ l ∧ (l : ℤ) ≤ k + 1 := by rcases hl with rfl | rfl <;> constructor <;> push_cast <;> omega
    have hlk' : (k : ℤ) ≤ l' ∧ (l' : ℤ) ≤ k + 1 := by
      rcases hl' with rfl | rfl <;> constructor <;> push_cast <;> omega
    have hs := densityProduct_split η q ((k : ℤ) - c) ((l : ℤ) - 1) n (by omega) (by omega)
    rw [sub_add_cancel] at hs
    have hP1 : 0 < densP η q l n := densityProduct_pos η hη q hq _ _ (by omega)
    have hP2 : 0 < densP η q l' n := densityProduct_pos η hη q hq _ _ (by omega)
    have e : densP η q ((k : ℤ) - c) n / (densP η q l n * densP η q l' n) =
        densP η q ((k : ℤ) - c) ((l : ℤ) - 1) * (densP η q l' n)⁻¹ := by
      rw [hs]; field_simp
    rw [e]
    have b1 := densityProduct_le_exp η hη q hq ((k : ℤ) - c) ((l : ℤ) - 1) (by omega)
    have b2 := densityProduct_inv_le_exp η hη q hq l' n (by omega)
    have b3 : 0 ≤ densP η q ((k : ℤ) - c) ((l : ℤ) - 1) := (densityProduct_pos η hη q hq _ _ (by omega)).le
    calc _ ≤ Real.exp (∑ i ∈ Finset.Icc ((k : ℤ) - c) ((l : ℤ) - 1), (q : ℝ) ^ (-i)) *
          Real.exp (∑ i ∈ Finset.Icc (l' : ℤ) n, 2 * (q : ℝ) ^ (-i)) :=
          mul_le_mul b1 b2 (inv_pos.2 hP2).le (Real.exp_pos _).le
      _ = Real.exp (∑ i ∈ Finset.Icc ((k : ℤ) - c) ((l : ℤ) - 1), (q : ℝ) ^ (-i) +
          ∑ i ∈ Finset.Icc (l' : ℤ) n, 2 * (q : ℝ) ^ (-i)) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.2
        rw [← Finset.mul_sum]
        have g1 := geom_le q hq ((k : ℤ) - c) ((l : ℤ) - 1)
        have g2 := geom_le q hq (l' : ℤ) n
        have m1 : (q : ℝ) ^ (-((k : ℤ) - c)) ≤ (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2)) :=
          zpow_le_zpow_right₀ (by linarith) (by omega)
        have m2 : (q : ℝ) ^ (-(l' : ℤ)) ≤ (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2) - 1) :=
          zpow_le_zpow_right₀ (by linarith) (by omega)
        have m3 : (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2)) = (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2) - 1) * q := by
          rw [← zpow_add_one₀ hq0.ne']; congr 1; ring
        have hp : 0 < (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2) - 1) := zpow_pos hq0 _
        nlinarith
end Formalism.FourierDecayAlt.P
