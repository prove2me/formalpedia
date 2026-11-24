-- Prove2me | solution 1 for Formalism.ZRN.tsum_er_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:43.249645+00:00
-- url     : https://prove2.me/submissions/73ed6d26-962b-405f-936c-625c02f83b10

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Theorems.Thm_Formalism_ZRN_er_nonneg
import Theorems.Thm_Formalism_ZRN_er_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) : ∑' n, er n σ ≤ 1 - σ := by
  refine Real.tsum_le_of_sum_range_le (fun n => er_nonneg n σ h0 h1) (fun N => ?_)
  let a : ℕ → ℝ := fun i => ((i : ℝ) + 1) ^ (-σ)
  have ha : ∀ i : ℕ, a (i + 1) = ((i : ℝ) + 2) ^ (-σ) := by
    intro i; simp only [a]; congr 1; push_cast; ring
  calc ∑ i ∈ Finset.range N, er i σ ≤ ∑ i ∈ Finset.range N, (1 - σ) * (a i - a (i + 1)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [ha]; exact er_le i σ h0 h1
    _ = (1 - σ) * (a 0 - a N) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ 1 - σ := by
        have : 0 ≤ a N := by simp only [a]; positivity
        have ha0 : a 0 = 1 := by simp [a]
        rw [ha0]; nlinarith
end Formalism.ZRN
