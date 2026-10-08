-- Prove2me | solution 1 for AvramDividend.Classical.cstarSet_closed_of_right_deriv_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:37:09.12204+00:00
-- url     : https://prove2.me/submissions/6f5bd044-bae4-4a46-8924-75369447777c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_deriv_near_zero_strict_of_liminf_gap
import Theorems.Thm_AvramDividend_Classical_cstarSet_closed_of_near_zero_deriv_gap

open AvramDividend.Classical Filter
open scoped Topology

theorem solution (W : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ cstarSet W)
    (hgap : ((deriv W a : ℝ) : EReal) < derivZeroPlus W)
    (hcont : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ))) :
    IsClosed (cstarSet W) := by
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), deriv W a < deriv W x :=
    deriv_near_zero_strict_of_liminf_gap W a hgap
  obtain ⟨δ, hδ, hnear⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  apply cstarSet_closed_of_near_zero_deriv_gap W a δ ha hδ
  · intro x hx hxδ
    exact hnear ⟨hx, hxδ⟩
  · exact hcont
