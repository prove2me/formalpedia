-- Prove2me | solution 1 for ConvexOptAlg.StochMD.thm_6_3_mirror_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:39:01.988331+00:00
-- url     : https://prove2.me/submissions/ee27c6f8-50a4-403b-bb4c-de9973c10c72

import Mathlib
import Definitions.Def_ConvexOptAlg_StochMD_Defs

set_option autoImplicit false

open ConvexOptAlg.StochMD in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D) (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (β η : ℝ) (hβ : 0 ≤ β) (hη : 0 < η)
    (xs xs1 : E) (g : E →L[ℝ] ℝ) (hxs : xs ∈ X ∩ D) (hxs1 : xs1 ∈ X ∩ D)
    (hstep : ∀ z ∈ X ∩ D,
      1 / (β + 1 / η) * g xs1 + bregman Φ Φ' xs1 xs ≤ 1 / (β + 1 / η) * g z + bregman Φ Φ' z xs)
    (xstar : E) (hxstar : xstar ∈ X) :
    1 / (β + 1 / η) * g (xs1 - xstar) ≤
      bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1 - bregman Φ Φ' xs1 xs := by
  obtain ⟨hDopen, hDconv, -, hder, -, -⟩ := hΦ
  set γ : ℝ := 1 / (β + 1 / η) with hγ
  set v : E := xstar - xs1 with hv
  let f : E → ℝ := fun z => γ * g z + bregman Φ Φ' z xs
  let L : E →L[ℝ] ℝ := γ • g + (Φ' xs1 - Φ' xs)
  have hf : HasFDerivAt f L xs1 := by
    have h1 : HasFDerivAt (fun z => γ * g z) (γ • g) xs1 := by
      exact (g.hasFDerivAt (x := xs1)).const_mul γ
    have h2 : HasFDerivAt (fun z => Φ z - Φ xs - (Φ' xs z - Φ' xs xs)) (Φ' xs1 - Φ' xs) xs1 := by
      have := (((hder xs1 hxs1.2).sub_const (Φ xs)).sub
        ((Φ' xs).hasFDerivAt.sub_const (Φ' xs xs)))
      exact this
    have h3 := h1.add h2
    have hfe : f = fun z => γ * g z + (Φ z - Φ xs - (Φ' xs z - Φ' xs xs)) := by
      funext z; simp [f, bregman, map_sub]
    rw [hfe]
    exact h3
  have hmin : IsLocalMinOn f (X ∩ D) xs1 := by
    apply IsMinOn.localize
    intro z hz
    exact hstep z hz
  have hseg : segment ℝ xs1 (xs1 + (1/2 : ℝ) • v) ⊆ X ∩ D := by
    rw [segment_eq_image']
    rintro _ ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    have hpt : xs1 + θ • (xs1 + (1/2 : ℝ) • v - xs1) = xs1 + (θ / 2) • (xstar - xs1) := by
      rw [hv]; simp only [add_sub_cancel_left, smul_smul]; ring_nf
    show xs1 + θ • (xs1 + (1 / 2 : ℝ) • v - xs1) ∈ X ∩ D
    rw [hpt]
    refine ⟨hXconv.add_smul_sub_mem hxs1.1 hxstar ⟨by linarith, by linarith⟩, ?_⟩
    have hint : xstar + (1 - θ / 2) • (xs1 - xstar) ∈ interior D :=
      hDconv.add_smul_sub_mem_interior' (hXD hxstar) (by rw [hDopen.interior_eq]; exact hxs1.2)
        ⟨by linarith, by linarith⟩
    rw [hDopen.interior_eq] at hint
    convert hint using 1
    rw [sub_smul, one_smul, smul_sub, smul_sub]
    abel
  have hcone : (1/2 : ℝ) • v ∈ posTangentConeAt (X ∩ D) xs1 :=
    mem_posTangentConeAt_of_segment_subset hseg
  have hnn := hmin.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hcone
  have hLv : 0 ≤ L v := by
    rw [map_smul, smul_eq_mul] at hnn
    nlinarith
  simp only [L, hv, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub] at hLv
  simp only [bregman, map_sub]
  nlinarith [hLv]
