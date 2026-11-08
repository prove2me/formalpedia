-- Prove2me | solution 1 for CombOpt.MatchingPolytope.proposition_6_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:35:28.660973+00:00
-- url     : https://prove2.me/submissions/e5f08359-0b07-44b0-bd9e-c780149f9e9b

import Mathlib

theorem solution {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (hS : S.Finite)
    (v : ι → ℝ) (hv : v ∉ convexHull ℝ S) :
    ∃ (w : ι → ℝ) (t : ℝ), (∀ s ∈ convexHull ℝ S, w ⬝ᵥ s ≤ t) ∧ t < w ⬝ᵥ v := by
  classical
  obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ S)
    (hS.isClosed_convexHull ℝ) hv
  let w : ι → ℝ := fun i => f (fun j => if i = j then 1 else 0)
  have hw : ∀ x, f x = w ⬝ᵥ x := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (ι → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  refine ⟨w, u, fun s hs => ?_, ?_⟩
  · rw [← hw]; exact (hf s hs).le
  · rw [← hw]; exact hu
