-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_recursivePaletteStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/7cb8a602-75c8-442f-8d00-5359c4ac104e

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_stage_palette_packing_exp
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_recursivePaletteColouring_fin
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteGrowthBound_succ

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H a j : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a) (hj : j ≤ H) :
    ∃ (n : ℕ)
      (C : SimpleGraph.TopEdgeLabeling (Fin n)
        (Fin (j * (a * saturatedMatrixRows H)))),
      TriangleFree C ∧
        (∀ colour : Fin (j * (a * saturatedMatrixRows H)),
          (C.labelGraph colour).Colorable (j + 1)) ∧
        PaletteGrowthBound a (saturatedMatrixRows H) j n := by
  classical
  have hs : 0 < saturatedMatrixRows H := by
    simp [saturatedMatrixRows]
  induction j with
  | zero =>
      refine ⟨1, (by simpa using singletonZeroColouring), ?_, ?_, ?_⟩
      · intro colour
        exact Fin.elim0 (by simpa using colour)
      · intro colour
        exact Fin.elim0 (by simpa using colour)
      · simp [PaletteGrowthBound]
  | succ j ih =>
      obtain ⟨n, C, htriangle, hcolour, hgrowth⟩ := ih (by omega)
      obtain ⟨family, hfamily, hseparated, hstage⟩ :=
        exists_stage_palette_packing_exp (j + 1) a
          (saturatedMatrixRows H) (by omega) ha hs
      have hcard :
          ∀ P ∈ family, P.card = a * saturatedMatrixRows H := by
        intro P hP
        exact (Finset.mem_powersetCard.mp (hfamily hP)).2
      have hsubtract :
          (j + 1) * (a * saturatedMatrixRows H) -
            a * saturatedMatrixRows H =
              j * (a * saturatedMatrixRows H) := by
        simp [Nat.succ_mul]
      have hstep := @exists_recursivePaletteColouring_fin
        n ((j + 1) * (a * saturatedMatrixRows H))
        (a * saturatedMatrixRows H) (j + 1) H
      rw [hsubtract] at hstep
      obtain ⟨C', htriangle', hcolour'⟩ :=
        hstep C htriangle hcolour hH hj family hcard hseparated
      exact ⟨family.card * n, C', htriangle', hcolour',
        paletteGrowthBound_succ hstage hgrowth⟩
end ErdosProblems.MulticolourTriangleRamsey
