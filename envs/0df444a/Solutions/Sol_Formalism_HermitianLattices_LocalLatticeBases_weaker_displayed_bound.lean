-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.weaker_displayed_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:29.460567+00:00
-- url     : https://prove2.me/submissions/64fcc2f1-c2d5-4ce9-87fc-ea8dc3f52116

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : NonintegralMatrixPreservesThirdOverlattice := by
  unfold NonintegralMatrixPreservesThirdOverlattice
  refine ⟨?_, ?_, ?_⟩
  · intro l c
    refine ⟨fun _ => l 0, c + l 1, ?_⟩
    intro i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    push_cast
    ring
  · intro i
    refine ⟨0, ?_⟩
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    obtain ⟨z, hz⟩ := h 0 1
    simp at hz
    have h3 : (3 : ℚ) * z = 1 := by rw [hz]; norm_num
    have : (3 : ℤ) * z = 1 := by exact_mod_cast h3
    omega
end Formalism.HermitianLattices.LocalLatticeBases
