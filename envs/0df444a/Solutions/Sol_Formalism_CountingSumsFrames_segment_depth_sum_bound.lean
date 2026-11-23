-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_depth_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:23.349659+00:00
-- url     : https://prove2.me/submissions/9ba6628d-23e5-42e0-9853-c06945a876b3

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_window_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_derived_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_log_bounds_of_nine_le
import Theorems.Thm_Formalism_CountingSumsFrames_log_seg_le_four_logb
import Theorems.Thm_Formalism_CountingSumsFrames_depth_le_square_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SegDepthSum := by
  intro p N N₁ r Y a b' Q La h Jn s t hJ hst
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  obtain ⟨hlp, hl1, hla⟩ := log_bounds_of_nine_le hp9 hpa
  obtain ⟨hlg0, hlg4⟩ := log_seg_le_four_logb (r := r) hp9 hpa (by linarith)
  have hj : ∀ j, DjSeg p N r (s j) (t j) Y a ≤
      45 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r + kap0I p N (r + 1) a :=
    fun j => depth_le_square_bound hY hK hN1' (hst j).1 (hst j).2 hlg0
  have hk0 : kap0I p N (r + 1) a = 2 * N * ((r : ℝ) + 1) * Real.logb p a := by
    unfold kap0I; push_cast; ring
  rw [hk0] at hj
  generalize lgSeg p a r = lg at *
  generalize Real.logb p a = L at *
  generalize (r : ℝ) + 1 = K at *
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hM2 : (N₁ : ℝ) ^ 2 ≤ K :=
    le_trans (pow_le_pow_right₀ hN1' (by norm_num)) hN1
  have e1 : 45 * Y ^ 2 * (N₁ : ℝ) ^ 2 * K ^ 2 * lg ≤ 45 * Y ^ 2 * K * K ^ 2 * (4 * L) := by gcongr
  have e2 : 2 * (N : ℝ) * K * L ≤ 2 * Y ^ 2 * K ^ 3 * L := by
    calc 2 * (N : ℝ) * K * L ≤ 2 * K * K * L := by gcongr
      _ = 2 * 1 * (K ^ 2 * 1) * L := by ring
      _ ≤ 2 * Y ^ 2 * (K ^ 2 * K) * L := by gcongr; linarith
      _ = 2 * Y ^ 2 * K ^ 3 * L := by ring
  have hB : 45 * Y ^ 2 * (N₁ : ℝ) ^ 2 * K ^ 2 * lg + 2 * N * K * L ≤ 182 * Y ^ 2 * K ^ 3 * L := by
    have : 45 * Y ^ 2 * K * K ^ 2 * (4 * L) = 180 * Y ^ 2 * K ^ 3 * L := by ring
    linarith
  have hJ' : (Jn : ℝ) ≤ N := by exact_mod_cast hJ
  calc ∑ j, DjSeg p N r (s j) (t j) Y a ≤ ∑ _j : Fin Jn, 182 * Y ^ 2 * K ^ 3 * L :=
        Finset.sum_le_sum (fun j _ => (hj j).trans hB)
    _ = Jn * (182 * Y ^ 2 * K ^ 3 * L) := by simp
    _ ≤ N * (182 * Y ^ 2 * K ^ 3 * L) := by gcongr
    _ = 182 * N * Y ^ 2 * K ^ 3 * L := by ring
end Formalism.CountingSumsFrames
