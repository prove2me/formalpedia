-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.accT_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:27.90581+00:00
-- url     : https://prove2.me/submissions/c7b26ab0-27d5-451a-b26d-d123a99a9908

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
theorem _root_.solution {V : ℕ} (a b c : Fin V → ℕ) (m c₀ : ℕ) {B : Finset (Fin V)}
    (i : Fin V → ℕ) {v : Fin V} (hv : v ∈ B) (u : Fin V) :
    accT a b c m c₀ B (Function.update i v (i v + 1)) u =
      accT a b c m c₀ B i u + if u = v then c v + c₀ else 0 := by

  by_cases huv : u = v
  · subst huv
    simp [accT, hv] <;> ring
  · simp [accT, Function.update_apply, huv]
end Formalism.G0.WalkSharpP
