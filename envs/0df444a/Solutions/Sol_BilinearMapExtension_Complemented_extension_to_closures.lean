-- Prove2me | solution 1 for BilinearMapExtension.Complemented.extension_to_closures
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:52:47.968488+00:00
-- url     : https://prove2.me/submissions/4003f613-3bc8-4715-a264-82f73154db87

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

namespace BilinearMapExtension.Complemented.ClosureProof

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

noncomputable def closureInclusion (M : Submodule 𝕜 X) :
    M →ₗᵢ[𝕜] M.topologicalClosure where
  toLinearMap := Submodule.inclusion M.le_topologicalClosure
  norm_map' _ := rfl

lemma closureInclusion_dense (M : Submodule 𝕜 X) :
    DenseRange (closureInclusion M) :=
  (denseRange_inclusion_iff M.le_topologicalClosure).mpr (by rfl)

lemma norm_extend_isometry [CompleteSpace Z]
    (T : X →L[𝕜] Z) (e : X →ₗᵢ[𝕜] Y) (he : DenseRange e) :
    ‖T.extend e.toContinuousLinearMap‖ = ‖T‖ := by
  apply le_antisymm
  · simpa using T.opNorm_extend_le (N := 1) he (fun x => by simp)
  · apply T.opNorm_le_bound (norm_nonneg _)
    intro x
    calc
      ‖T x‖ = ‖T.extend e.toContinuousLinearMap (e x)‖ := by
        exact congrArg norm (ContinuousLinearMap.extend_eq T
          (e := e.toContinuousLinearMap) he e.isometry.isUniformInducing x).symm
      _ ≤ ‖T.extend e.toContinuousLinearMap‖ * ‖e x‖ :=
        (T.extend e.toContinuousLinearMap).le_opNorm (e x)
      _ = ‖T.extend e.toContinuousLinearMap‖ * ‖x‖ := by rw [e.norm_map]

end BilinearMapExtension.Complemented.ClosureProof

theorem solution {𝕜 : Type*} [RCLike 𝕜] {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
    (M : Submodule 𝕜 X) (N : Submodule 𝕜 Y) (φ : M →L[𝕜] N →L[𝕜] Z) :
    ∃ φt : M.topologicalClosure →L[𝕜] N.topologicalClosure →L[𝕜] Z,
      (∀ (u : M) (v : N), φt (Submodule.inclusion M.le_topologicalClosure u)
        (Submodule.inclusion N.le_topologicalClosure v) = φ u v) ∧ ‖φt‖ = ‖φ‖ := by
  let eM : M →ₗᵢ[𝕜] M.topologicalClosure := BilinearMapExtension.Complemented.ClosureProof.closureInclusion M
  let eN : N →ₗᵢ[𝕜] N.topologicalClosure := BilinearMapExtension.Complemented.ClosureProof.closureInclusion N
  have hM : DenseRange eM := BilinearMapExtension.Complemented.ClosureProof.closureInclusion_dense M
  have hN : DenseRange eN := BilinearMapExtension.Complemented.ClosureProof.closureInclusion_dense N
  let T : M.topologicalClosure →L[𝕜] N →L[𝕜] Z := φ.extend eM.toContinuousLinearMap
  let U : N.topologicalClosure →L[𝕜] M.topologicalClosure →L[𝕜] Z := T.flip.extend eN.toContinuousLinearMap
  refine ⟨U.flip, ?_, ?_⟩
  · intro u v
    change U (eN v) (eM u) = φ u v
    rw [show U (eN v) = T.flip v from
      ContinuousLinearMap.extend_eq T.flip (e := eN.toContinuousLinearMap) hN eN.isometry.isUniformInducing v]
    change T (eM u) v = φ u v
    rw [show T (eM u) = φ u from
      ContinuousLinearMap.extend_eq φ (e := eM.toContinuousLinearMap) hM eM.isometry.isUniformInducing u]
  · simp only [ContinuousLinearMap.opNorm_flip]
    rw [show ‖U‖ = ‖T.flip‖ from
      BilinearMapExtension.Complemented.ClosureProof.norm_extend_isometry T.flip eN hN]
    rw [ContinuousLinearMap.opNorm_flip]
    exact BilinearMapExtension.Complemented.ClosureProof.norm_extend_isometry φ eM hM
