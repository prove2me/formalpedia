-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.expo_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:28.963291+00:00
-- url     : https://prove2.me/submissions/afae2b93-7a97-4342-b16a-ac3a8e2dcdb0

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
namespace Formalism.G0.WalkSharpP
theorem _root_.solution {V : ℕ} (m : ℕ) {B : Finset (Fin V)} (i : Fin V → ℕ) {v : Fin V}
    (hv : v ∈ B) (u : Fin V) :
    expo m B (Function.update i v (i v + 1)) u = expo m B i u + if u = v then 1 else 0 := by

  simp only [expo]
  by_cases huv : u = v
  · subst huv
    simp [hv]
  · simp [Function.update_apply, huv]
end Formalism.G0.WalkSharpP
