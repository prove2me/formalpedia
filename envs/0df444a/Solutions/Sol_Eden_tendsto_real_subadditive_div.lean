-- Prove2me | solution 1 for Eden.tendsto_real_subadditive_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:30.052212+00:00
-- url     : https://prove2.me/submissions/17eff0c7-1666-447c-a0d7-615bdbd6c0eb

import Definitions.Def_Eden_GlobalGrowth
import Mathlib.Analysis.Subadditive
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_Eden_RealSubadditive
import Theorems.Thm_Eden_real_subadditive_eventually_div_lt

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {f : ℝ → ℝ} {C : ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    (hC : 0 ≤ C) (hbound : ∀ t, 0 ≤ t → |f t| ≤ C * t) :
    Tendsto (fun t : ℝ => f t / t) atTop
      (𝓝 (sInf ((fun T : ℝ => f T / T) '' Ioi 0))) := by
  have hne : ((fun T : ℝ => f T / T) '' Ioi 0).Nonempty :=
    ⟨f 1 / 1, 1, (show (1 : ℝ) ∈ Ioi 0 by norm_num), rfl⟩
  have hbelow : BddBelow ((fun T : ℝ => f T / T) '' Ioi 0) := by
    refine ⟨-C, ?_⟩
    rintro x ⟨T, hT, rfl⟩
    apply (le_div_iff₀ hT).2
    have hb := (abs_le.mp (hbound T hT.le)).1
    linarith
  refine tendsto_order.2 ⟨fun l hl => ?_, fun L hL => ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact hl.trans_le (csInf_le hbelow ⟨t, ht, rfl⟩)
  · obtain ⟨x, ⟨T, hT, rfl⟩, hx⟩ := exists_lt_of_csInf_lt hne hL
    exact real_subadditive_eventually_div_lt hsub hC hbound hT hx
end Eden
