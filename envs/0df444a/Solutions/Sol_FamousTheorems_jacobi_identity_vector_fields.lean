-- Prove2me | solution 1 for FamousTheorems.jacobi_identity_vector_fields
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:44:31.610171+00:00
-- url     : https://prove2.me/submissions/16ddc188-744a-437b-89ca-7df4a1f86a1c

import Mathlib

theorem solution {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (minSmoothness 𝕜 3) M] {U V W : (x : M) → TangentSpace I x}
    (hU : ContMDiff I I.tangent (minSmoothness 𝕜 2) fun x => (⟨x, U x⟩ : TangentBundle I M))
    (hV : ContMDiff I I.tangent (minSmoothness 𝕜 2) fun x => (⟨x, V x⟩ : TangentBundle I M))
    (hW : ContMDiff I I.tangent (minSmoothness 𝕜 2) fun x => (⟨x, W x⟩ : TangentBundle I M)) :
    VectorField.mlieBracket I U (VectorField.mlieBracket I V W) =
      VectorField.mlieBracket I (VectorField.mlieBracket I U V) W + VectorField.mlieBracket I V (VectorField.mlieBracket I U W) :=
  VectorField.leibniz_identity_mlieBracket hU hV hW
