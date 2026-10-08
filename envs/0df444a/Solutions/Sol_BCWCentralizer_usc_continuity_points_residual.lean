-- Prove2me | solution 1 for BCWCentralizer.usc_continuity_points_residual
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:38:22.570104+00:00
-- url     : https://prove2.me/submissions/b7b091c2-ff09-44ea-a91b-12fa1385ea59

import Mathlib

open scoped Topology

set_option autoImplicit false

open Metric Set Filter Topology in
theorem solution {B X : Type*} [TopologicalSpace B] [BaireSpace B]
    [MetricSpace X] [CompactSpace X] (h : B → TopologicalSpace.NonemptyCompacts X)
    (husc : ∀ b : B, ∀ U : Set X, IsOpen U → (h b : Set X) ⊆ U →
      ∀ᶠ b' in 𝓝 b, (h b' : Set X) ⊆ U) :
    {b : B | ContinuousAt h b} ∈ residual B := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  have := hDc.to_subtype
  let F : D × ℕ → Set B := fun i =>
    {b | ((h b : Set X) ∩ closedBall (i.1 : X) (1 / ((i.2 : ℝ) + 1))).Nonempty}
  have hFc : ∀ i, IsClosed (F i) := by
    intro i
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro b hb
    have hsub : (h b : Set X) ⊆ (closedBall (i.1 : X) (1 / ((i.2 : ℝ) + 1)))ᶜ := by
      intro x hx hx'
      exact hb ⟨x, hx, hx'⟩
    filter_upwards [husc b _ isClosed_closedBall.isOpen_compl hsub] with b' hb'
    rintro ⟨x, hx, hx'⟩
    exact hb' hx hx'
  let G : Set B := ⋂ i, (F i \ interior (F i))ᶜ
  have hG : G ∈ residual B := by
    refine countable_iInter_mem.2 fun i => ?_
    have hcl : IsClosed (F i \ interior (F i)) := (hFc i).sdiff isOpen_interior
    have hnd : IsNowhereDense (F i \ interior (F i)) := by
      rw [hcl.isNowhereDense_iff]
      refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
      have h1 : x ∈ interior (F i) := interior_mono diff_subset hx
      exact (interior_subset hx).2 h1
    obtain ⟨ho, hd⟩ := isClosed_isNowhereDense_iff_compl.1 ⟨hcl, hnd⟩
    exact residual_of_dense_open ho hd
  refine mem_of_superset hG ?_
  intro b hb
  simp only [G, mem_iInter, mem_compl_iff, mem_diff, not_and, not_not] at hb
  rw [mem_setOf_eq, ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by positivity)
  set r : ℝ := 1 / ((m : ℝ) + 1) with hr
  have hr0 : 0 < r := Nat.one_div_pos_of_nat
  have hcov : (h b : Set X) ⊆ ⋃ d : {d : D // b ∈ F (d, m)}, ball (d.1 : X) r := by
    intro x hx
    obtain ⟨d, hdD, hd⟩ := hDd.exists_dist_lt x hr0
    refine mem_iUnion.2 ⟨⟨⟨d, hdD⟩, ⟨x, hx, ?_⟩⟩, ?_⟩
    · show dist x d ≤ r; exact hd.le
    · rw [mem_ball]; exact hd
  obtain ⟨t, ht⟩ := (h b).isCompact.elim_finite_subcover _ (fun _ => isOpen_ball) hcov
  have hev : ∀ᶠ b' in 𝓝 b, ∀ d ∈ t, b' ∈ F (d.1, m) := by
    rw [Finset.eventually_all]
    intro d _
    exact mem_interior_iff_mem_nhds.1 (hb _ d.2)
  filter_upwards [hev, husc b _ isOpen_thickening (self_subset_thickening hr0 _)] with b' h1 h2
  rw [Metric.NonemptyCompacts.dist_eq]
  refine lt_of_le_of_lt (hausdorffDist_le_of_mem_dist (r := 2 * r) (by positivity) ?_ ?_)
    (by linarith)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 (h2 hx)
    exact ⟨y, hy, by linarith⟩
  · intro z hz
    obtain ⟨d, hdt, hzd⟩ := mem_iUnion₂.1 (ht hz)
    obtain ⟨y, hy, hyd⟩ := h1 d hdt
    refine ⟨y, hy, ?_⟩
    have := dist_triangle z (d.1 : X) y
    rw [mem_ball] at hzd
    rw [mem_closedBall] at hyd
    rw [dist_comm (d.1 : X) y] at this
    linarith
