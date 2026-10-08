-- Prove2me | solution 1 for AvramDividend.Classical.cstar_attained_of_pos_cstar_and_deriv_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:47:28.022726+00:00
-- url     : https://prove2.me/submissions/4aec94b8-b224-46ef-be19-0ce886ae2d60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstarSet_closed_of_near_zero_deriv_gap
import Theorems.Thm_AvramDividend_Classical_cstar_attained_of_compact_initial_minimizers

open AvramDividend.Classical
open scoped ENNReal

theorem solution (W : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ cstarSet W)
    (hcpos : 0 < (cstar W).toReal)
    (hcont : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ))) :
    (cstar W).toReal ∈ cstarSet W := by
  classical
  have hnonempty : (cstarSet W).Nonempty := ⟨a, ha⟩
  have hbound : ∀ x ∈ cstarSet W, (cstar W).toReal ≤ x := by
    intro x hx
    have hle : cstar W ≤ ENNReal.ofReal x := by
      unfold cstar
      rw [if_pos hnonempty]
      exact iInf_le_of_le x (iInf_le _ hx)
    have hr :
        (cstar W).toReal ≤ (ENNReal.ofReal x).toReal :=
      ENNReal.toReal_mono (by simp) hle
    simpa [ENNReal.toReal_ofReal hx.1.le] using hr
  have hgap : ∀ x : ℝ, 0 < x → x < (cstar W).toReal →
      deriv W a < deriv W x := by
    intro x hx hxsmall
    have hxnot : x ∉ cstarSet W := by
      intro hxmem
      exact (not_lt_of_ge (hbound x hxmem)) hxsmall
    have hax : deriv W a ≤ deriv W x := ha.2 x hx
    by_contra hn
    have hxa : deriv W x ≤ deriv W a := le_of_not_gt hn
    have heq : deriv W x = deriv W a := le_antisymm hxa hax
    apply hxnot
    refine ⟨hx, ?_⟩
    intro y hy
    rw [heq]
    exact ha.2 y hy
  have hclosed : IsClosed (cstarSet W) :=
    cstarSet_closed_of_near_zero_deriv_gap
      W a (cstar W).toReal ha hcpos hgap hcont
  have hcompact : IsCompact (cstarSet W ∩ Set.Icc 0 a) :=
    isCompact_Icc.of_isClosed_subset
      (hclosed.inter isClosed_Icc) Set.inter_subset_right
  exact cstar_attained_of_compact_initial_minimizers W a ha hcompact
