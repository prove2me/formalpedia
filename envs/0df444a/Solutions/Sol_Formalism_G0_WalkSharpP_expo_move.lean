-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.expo_move
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:50.887805+00:00
-- url     : https://prove2.me/submissions/573dfd16-1997-4829-9214-049fcfd42bd5

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Theorems.Thm_Formalism_G0_WalkSharpP_le_top
import Theorems.Thm_Formalism_G0_WalkSharpP_done_move

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
theorem _root_.solution {V : ℕ} {m : ℕ} {B : Finset (Fin V)} {i : Fin V → ℕ} {v w : Fin V}
    (hv : v ∈ B) (hiv : i v + 1 = m) (hw : (w : ℕ) = top B + 1) (hiw : i w = 0) (u : Fin V) :
    expo m (insert w (B.erase v)) (Function.update i v 0) u =
      expo m B i u + if u = v then 1 else 0 := by

  simp only [expo, done_move hv hw]
  by_cases huv : u = v
  · subst v
    have h1 : ¬((u : ℕ) < top B ∧ u ∉ B) := fun h => h.2 hv
    simp [h1, hv, hiv]
  · by_cases huw : u = w
    · subst w
      have hwB : u ∉ B := fun h => by have := le_top h; omega
      have h2 : ¬((u : ℕ) < top B) := by omega
      simp [huv, hwB, h2, hiw, Function.update_apply]
    · by_cases huB : u ∈ B
      · simp [huv, huw, huB, Function.update_apply]
      · simp [huv, huw, huB, Function.update_apply]
end Formalism.G0.WalkSharpP
