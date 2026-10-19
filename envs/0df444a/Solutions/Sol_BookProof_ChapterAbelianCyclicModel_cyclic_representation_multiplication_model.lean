-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:05:40.907424+00:00
-- url     : https://prove2.me/submissions/78eaa5b3-b8bc-43ce-bbd6-a82e50d0b190

import Definitions.Def_ChapterAbelianGelfandModel
import Mathlib
import Definitions.Def_ChapterAbelianCyclicModel

open BookProof.ChapterAbelianCyclicModel
open MeasureTheory Complex WeakDual
open scoped ComplexOrder
open BookProof.ChapterAbelianGelfandModel

theorem h44_no_iso (mu : Measure PUnit.{1}) [IsProbabilityMeasure mu] :
    ¬ Nonempty (Lp ℂ 2 mu ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2)) := by
  rintro ⟨U⟩
  have key : ∀ f g : Lp ℂ 2 mu, inner ℂ f g = inner ℂ (f PUnit.unit) (g PUnit.unit) := by
    intro f g
    rw [L2.inner_def, integral_unique]
    simp
  let e0 := U.symm (EuclideanSpace.single 0 1)
  let e1 := U.symm (EuclideanSpace.single 1 1)
  have h01 : inner ℂ e0 e1 = 0 := by
    simp only [e0, e1, LinearIsometryEquiv.inner_map_map]
    simp [EuclideanSpace.inner_single_left]
  have h00 : inner ℂ e0 e0 = 1 := by
    simp only [e0, LinearIsometryEquiv.inner_map_map]
    simp
  have h11 : inner ℂ e1 e1 = 1 := by
    simp only [e1, LinearIsometryEquiv.inner_map_map]
    simp
  rw [key] at h01 h00 h11
  set a := e0 PUnit.unit; set b := e1 PUnit.unit
  have ha : a ≠ 0 := by rintro h; rw [h] at h00; simp at h00
  have hb : b ≠ 0 := by rintro h; rw [h] at h11; simp at h11
  simp [inner, ha, hb] at h01

theorem solution : ¬ (∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hxi : ‖xi‖ = 1),
    ∃ (mu : Measure X) (_ : IsProbabilityMeasure mu) (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H),
      (∀ (g : C(X, ℂ)) (u : Lp ℂ 2 mu), U (mulRep mu g u) = pi g (U u)) ∧
      (∀ (g : C(X, ℂ)) (v : H), U.symm (pi g v) = mulRep mu g (U.symm v))) := by
  intro h
  let E := EuclideanSpace ℂ (Fin 2)
  let pi : C(PUnit.{1}, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E) :=
    (StarAlgHom.ofId ℂ (E →L[ℂ] E)).comp (ContinuousMap.evalStarAlgHom ℂ ℂ PUnit.unit)
  obtain ⟨mu, hmu, U, -⟩ := h pi (EuclideanSpace.single 0 1) (by rw [EuclideanSpace.norm_single]; simp)
  exact h44_no_iso mu ⟨U⟩
