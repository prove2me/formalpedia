-- Prove2me | solution 1 for Conway99Formal.R172Repaired.Transition.local_square_exists
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:17:01.173+00:00
-- url     : https://prove2.me/submissions/943c8f49-ce85-4980-9842-9eca45602b13

import Mathlib
import Definitions.Def_r172_repaired

set_option autoImplicit false

namespace Conway99Formal.R172Repaired

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Transition

variable {G : SimpleGraph V} [DecidableRel G.Adj] (p : Transition G)

theorem common_card (h : G.IsSRGWith 99 14 1 2) :
    (common G p.left p.right).card = 2 := by
  simpa [common, Set.toFinset_card] using
    h.of_not_adj p.outer_distinct p.outer_nonadj

theorem centre_common : p.centre ∈ common G p.left p.right := by
  simp only [common, Set.mem_toFinset, SimpleGraph.mem_commonNeighbors]
  exact ⟨p.centre_left.symm, p.centre_right.symm⟩

theorem q_pos : 1 ≤ p.q := by
  have hm : p.centre ∈ common G p.left p.right ∩ p.support :=
    Finset.mem_inter.mpr ⟨p.centre_common, p.centre_support⟩
  exact Finset.card_pos.mpr ⟨p.centre, hm⟩

theorem count (h : G.IsSRGWith 99 14 1 2) : p.wCommon.card + p.q = 2 := by
  simpa [wCommon, q] using
    (Finset.card_sdiff_add_card_inter (common G p.left p.right) p.support).trans
      (p.common_card h)

theorem q_one_or_two (h : G.IsSRGWith 99 14 1 2) : p.q = 1 ∨ p.q = 2 := by
  have hp := p.q_pos
  have hc := p.count h
  omega

theorem wCommon_zeroSupport {x : V} (hx : x ∈ p.wCommon) :
    x ∈ zeroSupport p.support p.triangle := by
  have hm := Finset.mem_sdiff.mp hx
  have ht : x ∉ p.triangle := by
    intro hxt
    exact p.no_triangle_common x hxt hm.1
  simp [zeroSupport, hm.2, ht]

theorem q_one_w_unique (h : G.IsSRGWith 99 14 1 2) (hq : p.q = 1) :
    ∃! x, x ∈ p.wCommon := by
  have hc : p.wCommon.card = 1 := by have := p.count h; omega
  exact Finset.card_eq_one_iff_existsUnique.mp hc

theorem q_two_w_empty (h : G.IsSRGWith 99 14 1 2) (hq : p.q = 2) :
    p.wCommon = ∅ := by
  have hc : p.wCommon.card = 0 := by have := p.count h; omega
  exact Finset.card_eq_zero.mp hc

theorem q_two_support_unique (hq : p.q = 2) :
    ∃! x, x ∈ common G p.left p.right ∩ p.support ∧ x ≠ p.centre := by
  let C := common G p.left p.right ∩ p.support
  have hc : C.card = 2 := hq
  have hs : p.centre ∈ C := Finset.mem_inter.mpr ⟨p.centre_common, p.centre_support⟩
  have he : (C.erase p.centre).card = 1 := by
    simp [Finset.card_erase_of_mem hs, hc]
  simpa only [C, Finset.mem_erase, and_comm] using
    (Finset.card_eq_one_iff_existsUnique.mp he)

/-- The support column of a zero-support vertex in the same graph. -/
theorem connector_in_wCommon {x : V} (hx : p.coreConnector x) :
    x ∈ p.wCommon := by
  have hs : x ∉ p.support := by
    have hu : x ∉ p.support ∪ p.triangle := by
      exact (Finset.mem_sdiff.mp (show x ∈ Finset.univ \ (p.support ∪ p.triangle) from hx.1)).2
    simp only [Finset.mem_union, not_or] at hu
    exact hu.1
  exact Finset.mem_sdiff.mpr
    ⟨by simpa [common, SimpleGraph.mem_commonNeighbors] using ⟨hx.2.1, hx.2.2.1⟩, hs⟩

theorem connector_implies_q_one (h : G.IsSRGWith 99 14 1 2)
    {x : V} (hx : p.coreConnector x) : p.q = 1 := by
  have hw : 0 < p.wCommon.card := Finset.card_pos.mpr ⟨x, p.connector_in_wCommon hx⟩
  have hc := p.count h
  have hp := p.q_pos
  omega

theorem connector_unique (h : G.IsSRGWith 99 14 1 2)
    {x y : V} (hx : p.coreConnector x) (hy : p.coreConnector y) : x = y := by
  obtain ⟨z, hz, hunique⟩ := p.q_one_w_unique h (p.connector_implies_q_one h hx)
  calc
    x = z := hunique x (p.connector_in_wCommon hx)
    _ = y := (hunique y (p.connector_in_wCommon hy)).symm

theorem q_two_no_connector (h : G.IsSRGWith 99 14 1 2) (hq : p.q = 2) :
    ¬ ∃ x, p.coreConnector x := by
  rintro ⟨x, hx⟩
  have := p.connector_implies_q_one h hx
  omega

/-- The ordered four vertices form an induced square. -/
theorem square_of_common {x : V} (hx : x ∈ common G p.left p.right)
    (hcx : p.centre ≠ x) (hn : ¬ G.Adj p.centre x) : p.inducedSquare x := by
  have hh : G.Adj p.left x ∧ G.Adj p.right x := by
    simpa only [common, Set.mem_toFinset, SimpleGraph.mem_commonNeighbors] using hx
  have ha : G.Adj p.left x := hh.1
  have hb : G.Adj p.right x := hh.2
  exact ⟨p.centre_left.ne, ha.ne, hb.ne', p.centre_right.ne', hcx, p.outer_distinct,
    p.centre_left, ha, hb.symm, p.centre_right.symm, hn, p.outer_nonadj⟩

theorem q_one_square (h : G.IsSRGWith 99 14 1 2) (hq : p.q = 1) :
    ∃ x ∈ zeroSupport p.support p.triangle, p.inducedSquare x := by
  obtain ⟨x, hx, _⟩ := p.q_one_w_unique h hq
  have hm := (Finset.mem_sdiff.mp hx).1
  have hw := p.wCommon_zeroSupport hx
  have hcx : p.centre ≠ x := by
    intro he
    subst x
    exact (Finset.mem_sdiff.mp hx).2 p.centre_support
  exact ⟨x, hw, p.square_of_common hm hcx (p.zero_transport x hm hw)⟩

theorem q_two_square (hq : p.q = 2) :
    ∃ x ∈ p.support, x ≠ p.centre ∧ p.inducedSquare x := by
  let C := common G p.left p.right ∩ p.support
  have hc : C.card = 2 := hq
  have hsc : p.centre ∈ C := Finset.mem_inter.mpr ⟨p.centre_common, p.centre_support⟩
  have he : (C.erase p.centre).card = 1 := by
    simp [Finset.card_erase_of_mem hsc, hc]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp he
  have hxe : x ∈ C.erase p.centre := by rw [hx]; simp
  have hxm : x ∈ C := (Finset.mem_erase.mp hxe).2
  have hxn : x ≠ p.centre := (Finset.mem_erase.mp hxe).1
  have hi := Finset.mem_inter.mp hxm
  exact ⟨x, hi.2, hxn, p.square_of_common hi.1 hxn.symm
    (p.second_support_nonadj x hi.1 hi.2 hxn)⟩

theorem q_two_row_codegree (hq : p.q = 2) :
    ∃ x ∈ p.support, x ≠ p.centre ∧
      ((zeroSupport p.support p.triangle).filter
        (fun w => G.Adj p.centre w ∧ G.Adj x w)).card = 2 := by
  obtain ⟨x, hxs, hxn, hsquare⟩ := p.q_two_square hq
  rcases hsquare with ⟨_, _, _, _, _, _, _, hla, hxr, _, _, _⟩
  have hxa : G.Adj x p.left := hla.symm
  have hxb : G.Adj x p.right := hxr
  have hsub : ({p.left, p.right} : Finset V) ⊆
      (zeroSupport p.support p.triangle).filter
        (fun w => G.Adj p.centre w ∧ G.Adj x w) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_filter.mpr ⟨p.left_zero, p.centre_left, hxa⟩
    · have : w = p.right := by simpa using hw
      subst w
      exact Finset.mem_filter.mpr ⟨p.right_zero, p.centre_right, hxb⟩
  have hlow : 2 ≤ ((zeroSupport p.support p.triangle).filter
      (fun w => G.Adj p.centre w ∧ G.Adj x w)).card := by
    calc
      2 = ({p.left, p.right} : Finset V).card :=
        (Finset.card_pair p.outer_distinct).symm
      _ ≤ _ := Finset.card_le_card hsub
  exact ⟨x, hxs, hxn, by have := p.row_codegree_cap x hxs hxn; omega⟩

theorem square_exists (h : G.IsSRGWith 99 14 1 2) :
    ∃ x, p.inducedSquare x := by
  rcases p.q_one_or_two h with hq | hq
  · obtain ⟨x, _, hx⟩ := p.q_one_square h hq
    exact ⟨x, hx⟩
  · obtain ⟨x, _, _, hx⟩ := p.q_two_square hq
    exact ⟨x, hx⟩

end Transition
end Conway99Formal.R172Repaired

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Conway99Formal.R172Repaired.Transition G)
    (h : G.IsSRGWith 99 14 1 2) :
    ∃ x, p.inducedSquare x := by
  exact Conway99Formal.R172Repaired.Transition.square_exists p h

#print axioms solution
