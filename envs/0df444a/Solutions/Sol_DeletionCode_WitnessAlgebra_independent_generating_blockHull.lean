-- Prove2me | solution 1 for DeletionCode.WitnessAlgebra.independent_generating_blockHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:31.803955+00:00
-- url     : https://prove2.me/submissions/9aaba6c8-f36c-42b2-9b10-c6cabad5c082

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
import Theorems.Thm_DeletionCode_GeneratingBlocks_generating_blockHull


set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessAlgebra
theorem _root_.solution {I : Type*} {L : ℕ}
    (v : SignedSupport.Gram L → ℤ) (G : I → SignedSupport.Gram L → ℤ)
    (rank : I → ℕ) (T : Set I) (hgen : GeneratingBlocks.Generating v G rank)
    (hind : LinearIndependent ℚ (fun i h => (G i h : ℚ))) :
    GeneratingBlocks.Generating v
      (fun i : GeneratingBlocks.blockHull G T => G i.val)
      (fun i : GeneratingBlocks.blockHull G T => rank i.val) ∧
    LinearIndependent ℚ
      (fun (i : GeneratingBlocks.blockHull G T) h => (G i.val h : ℚ)) := by
  exact ⟨GeneratingBlocks.generating_blockHull v G rank T hgen,
    hind.comp Subtype.val Subtype.val_injective⟩
end DeletionCode.WitnessAlgebra
