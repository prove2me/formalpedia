-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_attained_of_deriv_growth_both_ends
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:27:44.388043+00:00
-- url     : https://prove2.me/submissions/04755584-70b0-4804-b221-c4f751407183

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_minimizer
import Theorems.Thm_AvramDividend_Classical_cstar_attained_of_strict_nearzero_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set
open scoped Topology ENNReal

theorem solution (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (deriv W) (Set.Ioi 0))
    (hzero : Filter.Tendsto (deriv W) (𝓝[>] (0 : ℝ)) Filter.atTop)
    (hinfty : Filter.Tendsto (deriv W) Filter.atTop Filter.atTop) :
    cstar W < ⊤ ∧ (cstar W).toReal ∈ cstarSet W := by
  have hnearev :
      {x : ℝ | deriv W a < deriv W x} ∈ 𝓝[>] (0 : ℝ) :=
    hzero.eventually_gt_atTop (deriv W a)
  obtain ⟨δ, hδmem, hδsubset⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset ha).1 hnearev
  have hδ0 : 0 < δ := hδmem.1
  have hδa : δ ≤ a := hδmem.2
  obtain ⟨R, hR⟩ :=
    Filter.eventually_atTop.1 (hinfty.eventually_ge_atTop (deriv W a))
  let M : ℝ := max a R + 1
  have haM : a < M := by
    dsimp [M]
    have hm := le_max_left a R
    linarith
  have hRM : R ≤ M := by
    dsimp [M]
    have hm := le_max_right a R
    linarith
  have hhalf : 0 < δ / 2 := half_pos hδ0
  have hhalfa : δ / 2 < a := (half_lt_self hδ0).trans_le hδa
  have hnear : ∀ x : ℝ, 0 < x → x < δ / 2 →
      deriv W a < deriv W x := by
    intro x hx hxδ
    exact hδsubset ⟨hx, hxδ.trans (half_lt_self hδ0)⟩
  have hane : a ∈ Set.Icc (δ / 2) M := ⟨hhalfa.le, haM.le⟩
  have hsubset : Set.Icc (δ / 2) M ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le hhalf hx.1
  obtain ⟨b, hb, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨a, hane⟩ (hcont.mono hsubset)
  have hbpos : 0 < b := lt_of_lt_of_le hhalf hb.1
  have hcomp : deriv W b ≤ deriv W a := hmin hane
  have hglobal : ∀ x : ℝ, 0 < x →
      deriv W b ≤ deriv W x := by
    intro x hx
    by_cases hxδ : x < δ / 2
    · exact hcomp.trans (le_of_lt (hnear x hx hxδ))
    · by_cases hMx : M < x
      · exact hcomp.trans (hR x (hRM.trans hMx.le))
      · exact hmin ⟨le_of_not_gt hxδ, le_of_not_gt hMx⟩
  have hbmem : b ∈ cstarSet W := ⟨hbpos, hglobal⟩
  have hshort : ContinuousOn (deriv W) (Set.Icc (δ / 2) b) :=
    hcont.mono (by
      intro x hx
      exact lt_of_lt_of_le hhalf hx.1)
  have hstrict : ∀ x : ℝ, 0 < x → x < δ / 2 →
      deriv W b < deriv W x := by
    intro x hx hxδ
    exact hcomp.trans_lt (hnear x hx hxδ)
  exact ⟨cstar_lt_top_of_minimizer W ⟨b, hbmem⟩,
    cstar_attained_of_strict_nearzero_bound
      W b (δ / 2) hbmem hhalf hb.1 hshort hstrict⟩
