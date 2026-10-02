-- Prove2me | solution 1 for BiconvexProg.Boundary.reflected_points_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:19:16.763738+00:00
-- url     : https://prove2.me/submissions/d103a275-e3f4-420f-8675-9169936f8712

import Mathlib
import Definitions.Def_BiconvexProg_Boundary_eucDist

set_option autoImplicit false

namespace BiconvexProg.Boundary

lemma eucDist_segment_14f {p q : ℕ}
    (z w : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) (t : ℝ) (ht : 0 ≤ t) :
    eucDist z (z + t • (w - z)) = t * eucDist z w := by
  unfold eucDist
  have h1 : ‖z.1 - (z + t • (w - z)).1‖ = t * ‖z.1 - w.1‖ := by
    have : z.1 - (z + t • (w - z)).1 = t • (z.1 - w.1) := by
      simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_sub]
      abel
    rw [this, norm_smul, Real.norm_of_nonneg ht]
  have h2 : ‖z.2 - (z + t • (w - z)).2‖ = t * ‖z.2 - w.2‖ := by
    have : z.2 - (z + t • (w - z)).2 = t • (z.2 - w.2) := by
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_sub]
      abel
    rw [this, norm_smul, Real.norm_of_nonneg ht]
  rw [h1, h2, show (t * ‖z.1 - w.1‖) ^ 2 + (t * ‖z.2 - w.2‖) ^ 2
      = t ^ 2 * (‖z.1 - w.1‖ ^ 2 + ‖z.2 - w.2‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

lemma eucDist_eq_zero_14f {p q : ℕ}
    {z w : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)} (h : eucDist z w = 0) :
    z = w := by
  unfold eucDist at h
  rw [Real.sqrt_eq_zero (by positivity)] at h
  have a1 : ‖z.1 - w.1‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖z.1 - w.1‖, sq_nonneg ‖z.2 - w.2‖]
  have a2 : ‖z.2 - w.2‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖z.1 - w.1‖, sq_nonneg ‖z.2 - w.2‖]
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at a1 a2
  exact Prod.ext a1 a2

lemma ball_sub_14f {p q : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q))) (hS : IsCompact S)
    (zbar zstar : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q))
    (hzbar : zbar ∈ interior S) (hzstar : zstar ∈ frontier S)
    (hnear : ∀ w ∈ frontier S, eucDist zbar zstar ≤ eucDist zbar w)
    (w : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q))
    (hw : eucDist zbar w ≤ eucDist zbar zstar) : w ∈ S := by
  have hclosed : IsClosed S := hS.isClosed
  have hr : 0 < eucDist zbar zstar := by
    rcases (Real.sqrt_nonneg _ : 0 ≤ eucDist zbar zstar).lt_or_eq with h | h
    · exact h
    · exfalso
      have he := eucDist_eq_zero_14f h.symm
      rw [he] at hzbar
      exact hzstar.2 hzbar
  by_contra hwS
  set f : ℝ → EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) :=
    fun t => zbar + t • (w - zbar) with hf
  have hcont : Continuous f := by fun_prop
  have hpc : IsPreconnected (f '' Set.Icc 0 1) :=
    isPreconnected_Icc.image f hcont.continuousOn
  have hf1 : f 1 = w := by simp [hf]
  have hf0 : f 0 = zbar := by simp [hf]
  by_cases hfr : (f '' Set.Icc 0 1 ∩ frontier S).Nonempty
  · obtain ⟨v, ⟨t, ⟨ht0, ht1⟩, rfl⟩, hv⟩ := hfr
    have h1 := hnear _ hv
    have hd : eucDist zbar (f t) = t * eucDist zbar w := eucDist_segment_14f zbar w t ht0
    rw [hd] at h1
    have hwn : 0 ≤ eucDist zbar w := Real.sqrt_nonneg _
    have hwpos : 0 < eucDist zbar w := by nlinarith
    have ht : t = 1 := by
      by_contra htne
      have : t < 1 := lt_of_le_of_ne ht1 htne
      nlinarith
    rw [ht, hf1] at hv
    exact hwS (hclosed.closure_eq ▸ frontier_subset_closure hv)
  · have hsub : f '' Set.Icc 0 1 ⊆ interior S ∪ (closure S)ᶜ := by
      intro x hx
      by_contra hc
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hc
      exact hfr ⟨x, hx, ⟨hc.2, hc.1⟩⟩
    have hdisj : Disjoint (interior S) (closure S)ᶜ := by
      rw [Set.disjoint_compl_right_iff_subset]
      exact interior_subset.trans subset_closure
    have hne : (f '' Set.Icc 0 1 ∩ interior S).Nonempty :=
      ⟨zbar, ⟨0, ⟨le_rfl, zero_le_one⟩, hf0⟩, hzbar⟩
    have hs := IsPreconnected.subset_left_of_subset_union isOpen_interior
      isClosed_closure.isOpen_compl hdisj hsub hne hpc
    have hwI : w ∈ f '' Set.Icc 0 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, hf1⟩
    exact hwS (interior_subset (hs hwI))

end BiconvexProg.Boundary

open BiconvexProg.Boundary in
theorem solution {p q : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q))) (hS : IsCompact S)
    (zbar zstar : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q))
    (hzbar : zbar ∈ interior S) (hzstar : zstar ∈ frontier S)
    (hnear : ∀ w ∈ frontier S, eucDist zbar zstar ≤ eucDist zbar w) :
    (∀ w, eucDist zbar w ≤ eucDist zbar zstar → w ∈ S) ∧
    ((2 : ℝ) • zbar.1 - zstar.1, (2 : ℝ) • zbar.2 - zstar.2) ∈ S ∧
    (zstar.1, (2 : ℝ) • zbar.2 - zstar.2) ∈ S ∧
    ((2 : ℝ) • zbar.1 - zstar.1, zstar.2) ∈ S := by
  have hball : ∀ w, eucDist zbar w ≤ eucDist zbar zstar → w ∈ S :=
    fun w hw => ball_sub_14f S hS zbar zstar hzbar hzstar hnear w hw
  have e1 : ‖zbar.1 - ((2 : ℝ) • zbar.1 - zstar.1)‖ = ‖zbar.1 - zstar.1‖ := by
    rw [show zbar.1 - ((2 : ℝ) • zbar.1 - zstar.1) = -(zbar.1 - zstar.1) by
      rw [two_smul]; abel, norm_neg]
  have e2 : ‖zbar.2 - ((2 : ℝ) • zbar.2 - zstar.2)‖ = ‖zbar.2 - zstar.2‖ := by
    rw [show zbar.2 - ((2 : ℝ) • zbar.2 - zstar.2) = -(zbar.2 - zstar.2) by
      rw [two_smul]; abel, norm_neg]
  refine ⟨hball, hball _ ?_, hball _ ?_, hball _ ?_⟩
  · apply le_of_eq
    unfold eucDist
    dsimp only
    rw [e1, e2]
  · apply le_of_eq
    unfold eucDist
    dsimp only
    rw [e2]
  · apply le_of_eq
    unfold eucDist
    dsimp only
    rw [e1]
