-- Prove2me | solution 1 for CursoEDO.lipschitzInSecondVar_of_bounded_partial_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T14:07:49.831014+00:00
-- url     : https://prove2.me/submissions/be12ec9b-9c52-4cb3-bd87-c03fe16311f9

import Mathlib
import Definitions.Def_CursoEDO_Defs

open CursoEDO

theorem solution
    {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
    [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    (U : Set (E₁ × E₂)) (hUopen : IsOpen U) (hUconv : Convex ℝ U)
    (f : E₁ × E₂ → E₃) (f₂ : E₁ × E₂ → (E₂ →L[ℝ] E₃)) (c : ℝ) (hc : 0 < c)
    (hderiv : ∀ p ∈ U, HasFDerivAt (fun y : E₂ => f (p.1, y)) (f₂ p) p.2)
    (hbound : ∀ p ∈ U, ‖f₂ p‖ ≤ c) :
    LipschitzInSecondVar U f c := by
  refine ⟨hc, ?_⟩
  intro z y₁ y₂ h₁ h₂
  set s : Set E₂ := {y : E₂ | (z, y) ∈ U} with hs
  have hsconv : Convex ℝ s := by
    intro u hu v hv a b ha hb hab
    have hz : a • z + b • z = z := by rw [← add_smul, hab, one_smul]
    have hpair : (z, a • u + b • v) = a • (z, u) + b • (z, v) := by
      simp [hz]
    have : (z, a • u + b • v) ∈ U := by
      rw [hpair]; exact hUconv hu hv ha hb hab
    exact this
  have hd : ∀ y ∈ s, HasFDerivWithinAt (fun y : E₂ => f (z, y)) (f₂ (z, y)) s y := by
    intro y hy
    exact (hderiv (z, y) hy).hasFDerivWithinAt
  have hb' : ∀ y ∈ s, ‖f₂ (z, y)‖ ≤ c := fun y hy => hbound (z, y) hy
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb' hsconv h₂ h₁
