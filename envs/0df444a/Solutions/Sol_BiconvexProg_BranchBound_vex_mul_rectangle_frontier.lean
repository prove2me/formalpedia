-- Prove2me | solution 1 for BiconvexProg.BranchBound.vex_mul_rectangle_frontier
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:13:30.606093+00:00
-- url     : https://prove2.me/submissions/02015974-0097-468a-8e03-c5be513436e0

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope

namespace BiconvexProg.BranchBound

theorem aux_vmrf_affine_convex (l L m M a b c : ℝ) :
    ConvexOn ℝ (Set.Icc l L ×ˢ Set.Icc m M) (fun q : ℝ × ℝ => a * q.1 + b * q.2 + c) := by
  refine ⟨(convex_Icc l L).prod (convex_Icc m M), ?_⟩
  intro x _ y _ s t _ _ hst
  apply le_of_eq
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have : c = s * c + t * c := by rw [← add_mul, hst, one_mul]
  linear_combination this

theorem aux_vmrf_boundary (l L m M : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ frontier (Set.Icc l L ×ˢ Set.Icc m M)) :
    p ∈ Set.Icc l L ×ˢ Set.Icc m M ∧ (p.1 = l ∨ p.1 = L ∨ p.2 = m ∨ p.2 = M) := by
  have hcl : IsClosed (Set.Icc l L ×ˢ Set.Icc m M) := isClosed_Icc.prod isClosed_Icc
  have h1 : p ∈ Set.Icc l L ×ˢ Set.Icc m M := hcl.frontier_subset hp
  refine ⟨h1, ?_⟩
  have h2 : p ∉ interior (Set.Icc l L ×ˢ Set.Icc m M) := hp.2
  rw [interior_prod_eq, interior_Icc, interior_Icc] at h2
  obtain ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩ := h1
  by_contra hne
  push Not at hne
  obtain ⟨e1, e2, e3, e4⟩ := hne
  exact h2 ⟨⟨lt_of_le_of_ne ha (Ne.symm e1), lt_of_le_of_ne hb e2⟩,
    ⟨lt_of_le_of_ne hc (Ne.symm e3), lt_of_le_of_ne hd e4⟩⟩

end BiconvexProg.BranchBound

open BiconvexProg.BranchBound

theorem solution (l L m M : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ frontier (Set.Icc l L ×ˢ Set.Icc m M)) :
    convexEnvelope (Set.Icc l L ×ˢ Set.Icc m M) (fun q : ℝ × ℝ => q.1 * q.2) p = p.1 * p.2 := by
  obtain ⟨hmem, hcases⟩ := aux_vmrf_boundary l L m M p hp
  unfold convexEnvelope
  apply IsGreatest.csSup_eq
  constructor
  · -- membership: pick a McCormick affine minorant that is tight at p
    have hlow : ∀ w ∈ Set.Icc l L ×ˢ Set.Icc m M,
        m * w.1 + l * w.2 + (-(l * m)) ≤ w.1 * w.2 := by
      rintro w ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h3)]
    have hup : ∀ w ∈ Set.Icc l L ×ˢ Set.Icc m M,
        M * w.1 + L * w.2 + (-(L * M)) ≤ w.1 * w.2 := by
      rintro w ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h4)]
    rcases hcases with h | h | h | h
    · exact ⟨_, aux_vmrf_affine_convex l L m M m l (-(l * m)), hlow, by rw [h]; ring⟩
    · exact ⟨_, aux_vmrf_affine_convex l L m M M L (-(L * M)), hup, by rw [h]; ring⟩
    · exact ⟨_, aux_vmrf_affine_convex l L m M m l (-(l * m)), hlow, by rw [h]; ring⟩
    · exact ⟨_, aux_vmrf_affine_convex l L m M M L (-(L * M)), hup, by rw [h]; ring⟩
  · rintro r ⟨g, _, hg, rfl⟩
    exact hg p hmem
