-- Prove2me | solution 1 for Formalism.CountingSumsFrames.tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:55.192823+00:00
-- url     : https://prove2.me/submissions/785a27b3-bed2-4f70-a418-33def2f3f911

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_mono
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_ratio

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
theorem _root_.solution (k' A B J : ℕ) (hJ : J ≤ min A B) :
    ((dimPol k' (A - J) * dimPol k' (B - J) : ℕ) : ℝ) ≤
      (1 - (J : ℝ) / (B + k' + 1)) ^ k' * ((dimPol k' A * dimPol k' B : ℕ) : ℝ) := by
  have hJB' : J ≤ B := le_trans hJ (min_le_right A B)
  have hJB : (J:ℝ) ≤ B := by exact_mod_cast hJB'
  have hx0 : 0 ≤ 1 - (J:ℝ) / ((B:ℝ) + k' + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have h1 : (dimPol k' (A - J) : ℝ) ≤ dimPol k' A := by
    exact_mod_cast dimPol_mono k' (Nat.sub_le A J)
  have h2 := dimPol_ratio B J hJB' k'
  rw [Nat.cast_mul, Nat.cast_mul]
  calc (dimPol k' (A - J) : ℝ) * dimPol k' (B - J)
      ≤ dimPol k' A * ((1 - (J:ℝ) / ((B:ℝ) + k' + 1)) ^ k' * dimPol k' B) :=
        mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by ring
end Formalism.CountingSumsFrames
