-- Prove2me | solution 1 for CurvatureSubmod.CSSP.lemma_8_1_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:14:53.077497+00:00
-- url     : https://prove2.me/submissions/bb4bab03-f714-4698-9918-4d0e2d0eeda4

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting
set_option autoImplicit false
open CurvatureSubmod.CSSP

theorem norm_proj_mono {m : ℕ} {K L : Submodule ℝ (EuclideanSpace ℝ (Fin m))} (h : K ≤ L)
    (v : EuclideanSpace ℝ (Fin m)) :
    ‖K.starProjection v‖ ≤ ‖L.starProjection v‖ := by
  have := Submodule.starProjection_comp_starProjection_of_le h
  have h2 : K.starProjection (L.starProjection v) = K.starProjection v := by
    simpa using congrArg (fun T => T v) this
  calc ‖K.starProjection v‖ = ‖K.starProjection (L.starProjection v)‖ := by rw [h2]
    _ ≤ _ := Submodule.norm_starProjection_apply_le _ _

theorem colSpan_mono {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) {A B : Finset (Fin n)}
    (h : A ⊆ B) : colSpan c A ≤ colSpan c B :=
  Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

theorem proj_sq_mono {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) {A B : Finset (Fin n)}
    (h : A ⊆ B) (v : EuclideanSpace ℝ (Fin m)) :
    ‖proj c A v‖ ^ 2 ≤ ‖proj c B v‖ ^ 2 := by
  have := norm_proj_mono (colSpan_mono c h) v
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

theorem solution {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) :
    MonoInc (fun S : Finset (Fin n) => ‖proj c S v‖ ^ 2) := by
  intro A i
  unfold marg
  have := proj_sq_mono c (Finset.subset_insert i A) v
  simp only
  linarith

