-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ShapeDiagramLemmas.shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:47.781169+00:00
-- url     : https://prove2.me/submissions/5af4dc10-e1a1-4ee2-880e-2ce4487703da

import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_EdgeNoTrunc
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ThetaLogIsSubstitution
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ShapeDiagramLemmas_shape_al

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.ShapeDiagramLemmas
namespace Formalism.InvariantFactorPaths.G7.ShapeDiagramLemmas
theorem _root_.solution {ν : ℕ} (TT : Finset (ZMod (2 * ν))) (μ : ZMod (2 * ν) → YoungDiagram)
    (s : ZMod (2 * ν)) :
    alG TT (fun s => (μ s).rowLen 0) (fun s c => (μ s).colLen c) s =
        (if s ∈ TT then (μ s).rowLen 0 - (μ s).rowLen 1 else 0) ∧
    capG TT (fun s => (μ s).rowLen 0) (fun s c => (μ s).colLen c) s =
        (if s ∈ TT then (μ s).rowLen 1 else (μ s).rowLen 0) := by
  have h1 : (μ s).rowLen 1 ≤ (μ s).rowLen 0 := (μ s).rowLen_anti 0 1 (by omega)
  unfold capG alG
  split_ifs
  · rw [shape_al]; exact ⟨rfl, by dsimp only; omega⟩
  · exact ⟨rfl, rfl⟩
end Formalism.InvariantFactorPaths.G7.ShapeDiagramLemmas
