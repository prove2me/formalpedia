-- Prove2me | solution 1 for BookProof.NavierStokesFlow.eq_zero_of_deficiency_of_completeUnitaryFlow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:03.305243+00:00
-- url     : https://prove2.me/submissions/34c3d1e6-2d3e-4940-9f48-cef717fbce8d

-- Generated from ChapterNavierStokesEsa.lean — solution of BookProof.NavierStokesFlow.eq_zero_of_deficiency_of_completeUnitaryFlow
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_NavierStokesFlow_eq_zero_of_inner_right_eq_zero_on_dense
import Theorems.Thm_BookProof_NavierStokesFlow_eq_zero_of_hasDerivAt_smul_of_bounded
open BookProof.NavierStokesFlow









open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (D : Submodule ℂ F) (H : D →ₗ[ℂ] D)
    (U : ℝ → F → F) (hdense : Dense (D : Set F)) (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖)
    (hU0 : ∀ v : F, U 0 v = v) (hUD : ∀ (t : ℝ) (v : D), U t (v : F) ∈ D)
    (hderiv : ∀ (v : D) (t : ℝ),
      HasDerivAt (fun s => U s (v : F)) (Complex.I • (H ⟨U t (v : F), hUD t v⟩ : F)) t)
    (s : ℝ) (hs : s * s = 1) (w : F)
    (hw : ∀ v : D, (inner ℂ (H v : F) w : ℂ) = inner ℂ (v : F) (((s : ℂ) * Complex.I) • w)) :
    w = 0 := by

  refine eq_zero_of_inner_right_eq_zero_on_dense hdense w fun v => ?_
  set g : ℝ → ℂ := fun t => inner ℂ w (U t (v : F)) with hg
  have hgd : ∀ t : ℝ, HasDerivAt g ((s : ℂ) * g t) t := by
    intro t
    have h1 : HasDerivAt g (inner ℂ w (Complex.I • (H ⟨U t (v : F), hUD t v⟩ : F)) : ℂ) t :=
      ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hderiv v t)
    have h2 : (inner ℂ w (Complex.I • (H ⟨U t (v : F), hUD t v⟩ : F)) : ℂ) = (s : ℂ) * g t := by
      have hk := hw ⟨U t (v : F), hUD t v⟩
      have hc : (inner ℂ w (H ⟨U t (v : F), hUD t v⟩ : F) : ℂ)
          = starRingEnd ℂ (inner ℂ (H ⟨U t (v : F), hUD t v⟩ : F) w) := (inner_conj_symm _ _).symm
      rw [hk, inner_smul_right] at hc
      rw [inner_smul_right, hc]
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, inner_conj_symm, hg]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h2] at h1
    exact h1
  have hb : ∀ t : ℝ, ‖g t‖ ≤ ‖w‖ * ‖(v : F)‖ := fun t =>
    calc ‖g t‖ ≤ ‖w‖ * ‖U t (v : F)‖ := norm_inner_le_norm _ _
      _ = ‖w‖ * ‖(v : F)‖ := by rw [hnorm]
  simpa [hg, hU0] using eq_zero_of_hasDerivAt_smul_of_bounded g s (‖w‖ * ‖(v : F)‖) hs hgd hb
