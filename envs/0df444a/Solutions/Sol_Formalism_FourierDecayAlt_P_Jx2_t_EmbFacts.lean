-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.t_EmbFacts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:22.891412+00:00
-- url     : https://prove2.me/submissions/1497a28e-2893-4492-935d-e4a7c42c6407

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
namespace Formalism.FourierDecayAlt.P.Jx2
theorem _root_.solution : EmbFacts := by
  intro E _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    have h' : w.embedding a = w.embedding b := by
      simpa [cemb] using congrArg (fun x : CV E => x w) h
    exact w.embedding.injective h'
  · constructor
    · intro x y h
      ext w
      simpa [coord] using congrFun h w
    · intro f
      exact ⟨WithLp.toLp 2 f, by funext w; simp [coord]⟩
  · intro t w
    simp [coord, cemb, InfinitePlace.norm_embedding_eq]
  · intro c t
    rfl
  · intro g c l w
    simp [coord, dm, InfinitePlace.norm_embedding_eq]
    left
    rw [abs_div, abs_mul, Nat.abs_cast, abs_two]
end Formalism.FourierDecayAlt.P.Jx2
