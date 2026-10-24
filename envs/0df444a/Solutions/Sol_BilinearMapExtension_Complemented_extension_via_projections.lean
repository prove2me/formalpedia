-- Prove2me | solution 1 for BilinearMapExtension.Complemented.extension_via_projections
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:52:50.254614+00:00
-- url     : https://prove2.me/submissions/d4093ddc-d647-4ab3-8daf-ef108334df2e

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

namespace BilinearMapExtension.Complemented.ProjectionProof

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Restricting both arguments cannot increase the bilinear operator norm. -/
theorem norm_mono_of_extension {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (M : Submodule 𝕜 X) (N : Submodule 𝕜 Y)
    (φ : M →L[𝕜] N →L[𝕜] Z) (φh : X →L[𝕜] Y →L[𝕜] Z)
    (h : IsBilinExtension M N φ φh) : ‖φ‖ ≤ ‖φh‖ := by
  apply φ.opNorm_le_bound₂ (norm_nonneg φh)
  intro u v
  rw [← h u v]
  exact φh.le_opNorm₂ u v

end BilinearMapExtension.Complemented.ProjectionProof

open BilinearMapExtension.Complemented

/-- Extension through bounded projections, with both operator-norm bounds. -/
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (M : Submodule 𝕜 X) (N : Submodule 𝕜 Y)
    (E : X →L[𝕜] X) (P : Y →L[𝕜] Y)
    (hE : IsProjectionOnto E M.topologicalClosure) (hP : IsProjectionOnto P N.topologicalClosure)
    (φ : M →L[𝕜] N →L[𝕜] Z)
    (φt : M.topologicalClosure →L[𝕜] N.topologicalClosure →L[𝕜] Z)
    (hφt : ∀ (u : M) (v : N), φt (Submodule.inclusion M.le_topologicalClosure u)
      (Submodule.inclusion N.le_topologicalClosure v) = φ u v) :
    ∃ φh : X →L[𝕜] Y →L[𝕜] Z,
      (∀ x y, φh x y = φt ⟨E x, hE.1 x⟩ ⟨P y, hP.1 y⟩) ∧ IsBilinExtension M N φ φh ∧
      ‖φ‖ ≤ ‖φh‖ ∧ ‖φh‖ ≤ ‖φt‖ * ‖E‖ * ‖P‖ := by
  let ER := E.codRestrict M.topologicalClosure hE.1
  let PR := P.codRestrict N.topologicalClosure hP.1
  let φh := ((ContinuousLinearMap.compL 𝕜 Y N.topologicalClosure Z).flip PR).comp
    (φt.comp ER)
  have happ : ∀ x y, φh x y = φt ⟨E x, hE.1 x⟩ ⟨P y, hP.1 y⟩ := by
    intro x y
    rfl
  have hext : IsBilinExtension M N φ φh := by
    intro u v
    rw [happ]
    have heu : (⟨E u, hE.1 u⟩ : M.topologicalClosure) =
        Submodule.inclusion M.le_topologicalClosure u := by
      apply Subtype.ext
      exact hE.2 u (M.le_topologicalClosure u.property)
    have hpv : (⟨P v, hP.1 v⟩ : N.topologicalClosure) =
        Submodule.inclusion N.le_topologicalClosure v := by
      apply Subtype.ext
      exact hP.2 v (N.le_topologicalClosure v.property)
    rw [heu, hpv]
    exact hφt u v
  refine ⟨φh, happ, hext, ProjectionProof.norm_mono_of_extension M N φ φh hext, ?_⟩
  apply φh.opNorm_le_bound₂ (by positivity)
  intro x y
  rw [happ]
  calc
    ‖φt ⟨E x, hE.1 x⟩ ⟨P y, hP.1 y⟩‖ ≤ ‖φt‖ * ‖E x‖ * ‖P y‖ :=
      φt.le_opNorm₂ _ _
    _ ≤ ‖φt‖ * (‖E‖ * ‖x‖) * (‖P‖ * ‖y‖) := by
      gcongr
      · exact E.le_opNorm x
      · exact P.le_opNorm y
    _ = ‖φt‖ * ‖E‖ * ‖P‖ * ‖x‖ * ‖y‖ := by ring
