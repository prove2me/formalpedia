-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_recursivePaletteColouring_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/dcfd4b88-a5a4-463b-9e4c-3352525d610f

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_cliqueFree_pullback_embedding
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_colorable_pullback_embedding
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_PaletteBlockCertificate_noMonochromaticTriangle
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_PaletteBlockCertificate_colourGraph_colorable
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_coordinate_covering

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution
    {n N t j H : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (N - t)))
    (htriangle : ∀ colour : Fin (N - t),
      (C.labelGraph colour).CliqueFree 3)
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hH : 2 ≤ H) (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated (saturatedMatrixRows H) family) :
    ∃ C' : SimpleGraph.TopEdgeLabeling
        (Fin (family.card * n)) (Fin N),
      TriangleFree C' ∧
        (∀ colour : Fin N, (C'.labelGraph colour).Colorable (j + 1)) := by
  classical
  obtain ⟨f, g, hcover⟩ := exists_coordinate_covering H hH
  let C' := recursivePaletteColouring C hC hj family hcard hseparated
    f g hcover
  let certificate := recursivePaletteCertificate C htriangle hC hj family
    hcard hseparated f g hcover
  have hproduct : Fintype.card (↥family × Fin n) = family.card * n := by
    simp
  let embedding : Fin (family.card * n) ↪ (↥family × Fin n) :=
    (Fintype.equivFinOfCardEq hproduct).symm.toEmbedding
  refine ⟨C'.pullback embedding, ?_, ?_⟩
  · exact cliqueFree_pullback_embedding C' embedding
      certificate.noMonochromaticTriangle
  · intro colour
    exact colorable_pullback_embedding C' embedding colour
      (certificate.colourGraph_colorable colour)
end ErdosProblems.MulticolourTriangleRamsey
