-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.densTyped_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:53.628987+00:00
-- url     : https://prove2.me/submissions/45f2bc74-0616-440b-b34a-6182ff8e31fe

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_factor_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_pos

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.DensTyped := by
  intro g k r c hg
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  set n : ℤ := ((k + 2 * r + 1 : ℕ) : ℤ) with hn
  have hnk : n = (k : ℤ) + 2 * r + 1 := by rw [hn]; push_cast; ring
  refine ⟨?_, ?_⟩
  · have hs := densityProduct_split 1 g ((k : ℤ) - c) k n (by omega) (by omega)
    have hP : 0 < densP 1 g ((k : ℤ) + 1) n := densityProduct_pos 1 (Or.inl rfl) g hg _ _ (by omega)
    rw [hs]
    have e : (g : ℝ) ^ (-(2 * ((r : ℤ) + 1) * ((k : ℤ) - 1))) * (g : ℝ) ^ (-(3 * ((r : ℤ) + 1) ^ 2)) =
        (g : ℝ) ^ (-(2 * ((k : ℤ) + 2 * r + 1) * ((r : ℤ) + 1) - ((r : ℤ) + 1) ^ 2)) := by
      rw [← zpow_add₀ hg0.ne']; congr 1; ring
    have hz : 0 < (g : ℝ) ^ (-(2 * ((k : ℤ) + 2 * r + 1) * ((r : ℤ) + 1) - ((r : ℤ) + 1) ^ 2)) :=
      zpow_pos hg0 _
    rw [div_eq_iff (by positivity), ← e]
    ring
  · rcases le_or_gt ((k : ℤ) - c) 0 with h0 | h0
    · rw [densityProduct_eq_zero 1 g _ _ h0 (by omega)]
      exact ⟨le_refl _, zero_le_one⟩
    · refine ⟨(densityProduct_pos 1 (Or.inl rfl) g hg _ _ (by omega)).le, ?_⟩
      unfold densP
      apply Finset.prod_le_one
      · intro i hi
        exact (factor_pos 1 (Or.inl rfl) g hg i (by have := (Finset.mem_Icc.1 hi).1; omega)).le
      · intro i hi
        have hpos : 0 < (g : ℝ) ^ (-i) := zpow_pos hg0 _
        simp only [Int.cast_one, one_zpow, one_mul]
        linarith
end Formalism.FourierDecayAlt.P
