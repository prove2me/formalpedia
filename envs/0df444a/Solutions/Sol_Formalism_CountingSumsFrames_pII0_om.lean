-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pII0_om
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:24.260878+00:00
-- url     : https://prove2.me/submissions/bcc4b45a-5ddc-4672-a3ee-e9f873168dcb

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
import Theorems.Thm_Formalism_CountingSumsFrames_pII0_one_le_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real
namespace Formalism.CountingSumsFrames
theorem _root_.solution (r N n' c₀ c'' : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) : (c₀ : ℝ) ≤ omII r N n' c₀ c'' := by
  unfold omII
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrN : (1 : ℝ) ≤ r * N := pII0_one_le_mul hr' hN'
  have hc : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * r * n' * c'' := by positivity
  nlinarith
end Formalism.CountingSumsFrames
