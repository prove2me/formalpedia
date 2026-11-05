-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_real_jordan_parts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:42:37.782239+00:00
-- url     : https://prove2.me/submissions/982c208a-7439-46ce-b7f9-1d46e583f7b3

import Mathlib.Topology.Algebra.Support
import Mathlib.Order.Lattice
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology AvramDividend.Classical

/-- Real Jordan decomposition preserving compact negative support. -/
theorem solution
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    ∃ gp gn : ℝ → ℝ,
      Continuous gp ∧ IsCompact (tsupport gp) ∧ tsupport gp ⊆ Iio (0 : ℝ) ∧
      Continuous gn ∧ IsCompact (tsupport gn) ∧ tsupport gn ⊆ Iio (0 : ℝ) ∧
      (∀ x : ℝ, 0 ≤ gp x ∧ 0 ≤ gn x ∧ g x = gp x - gn x) := by
  let gp : ℝ → ℝ := fun x => max (g x) 0
  let gn : ℝ → ℝ := fun x => max (-g x) 0
  have hgp : Continuous gp := hg.max continuous_const
  have hgn : Continuous gn := hg.neg.max continuous_const
  have hsp : Function.support gp ⊆ Function.support g := by
    intro x hx
    change g x ≠ 0
    intro hz
    apply hx
    simp [gp, hz]
  have hsn : Function.support gn ⊆ Function.support g := by
    intro x hx
    change g x ≠ 0
    intro hz
    apply hx
    simp [gn, hz]
  have htp : tsupport gp ⊆ tsupport g := closure_mono hsp
  have htn : tsupport gn ⊆ tsupport g := closure_mono hsn
  have hcp : IsCompact (tsupport gp) :=
    hc.of_isClosed_subset (isClosed_tsupport gp) htp
  have hcn : IsCompact (tsupport gn) :=
    hc.of_isClosed_subset (isClosed_tsupport gn) htn
  refine ⟨gp, gn, hgp, hcp, htp.trans hneg, hgn, hcn, htn.trans hneg, ?_⟩
  intro x
  constructor
  · exact le_max_right _ _
  constructor
  · exact le_max_right _ _
  rcases le_total 0 (g x) with h | h
  · have hn : -g x ≤ 0 := neg_nonpos.mpr h
    simp [gp, gn, max_eq_left h, max_eq_right hn]
  · have hn : 0 ≤ -g x := neg_nonneg.mpr h
    simp [gp, gn, max_eq_right h, max_eq_left hn]
