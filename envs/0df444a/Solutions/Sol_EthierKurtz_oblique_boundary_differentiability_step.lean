-- Prove2me | solution 1 for EthierKurtz.oblique_boundary_differentiability_step
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:10:37.963514+00:00
-- url     : https://prove2.me/submissions/5af8c7bc-3faf-4652-b525-2e73ee25d43f

import Mathlib

open scoped Topology

namespace EthierKurtz

theorem aux_obds_frontier :
    (0 : EuclideanSpace ℝ (Fin 1)) ∈ frontier ({0} : Set (EuclideanSpace ℝ (Fin 1))) := by
  rw [frontier, closure_singleton, interior_singleton]
  simp

end EthierKurtz

open EthierKurtz
open scoped Topology

theorem solution : ¬ (∀ {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    {J : (closure Ω) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)}
    (hx : x₀ ∈ frontier Ω) (hxmem : x₀ ∈ closure Ω)
    (hC : ContDiffOn ℝ 2 u Ω)
    (hcont : ContinuousOn u (closure Ω))
    (hJc : Continuous J)
    (hJid : ∀ x : (closure Ω), (x : EuclideanSpace ℝ (Fin d)) ∈ Ω →
      J x = fderiv ℝ u x),
    HasFDerivAt u (J ⟨x₀, hxmem⟩) x₀) := by
  intro h
  have hx : (0 : EuclideanSpace ℝ (Fin 1)) ∈ frontier ({0} : Set (EuclideanSpace ℝ (Fin 1))) :=
    aux_obds_frontier
  have hxmem : (0 : EuclideanSpace ℝ (Fin 1)) ∈ closure ({0} : Set (EuclideanSpace ℝ (Fin 1))) :=
    subset_closure rfl
  have hC : ContDiffOn ℝ 2 (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖)
      ({0} : Set (EuclideanSpace ℝ (Fin 1))) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact contDiffWithinAt_singleton
  have hcont : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖)
      (closure ({0} : Set (EuclideanSpace ℝ (Fin 1)))) :=
    continuous_norm.continuousOn
  have hJc : Continuous (fun _ : closure ({0} : Set (EuclideanSpace ℝ (Fin 1))) =>
      (0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) := continuous_const
  have hJid : ∀ x : closure ({0} : Set (EuclideanSpace ℝ (Fin 1))),
      (x : EuclideanSpace ℝ (Fin 1)) ∈ ({0} : Set (EuclideanSpace ℝ (Fin 1))) →
      (fun _ : closure ({0} : Set (EuclideanSpace ℝ (Fin 1))) =>
        (0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) x =
        fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖) x := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    simp only
    rw [hx, fderiv_zero_of_not_differentiableAt
      (not_differentiableAt_norm_zero (EuclideanSpace ℝ (Fin 1)))]
  have := h hx hxmem hC hcont hJc hJid
  exact not_differentiableAt_norm_zero (EuclideanSpace ℝ (Fin 1)) this.differentiableAt
