-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.accT_move
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:50.669823+00:00
-- url     : https://prove2.me/submissions/08d7f4e9-31a5-4f4f-9968-0595b27dbfad

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
theorem _root_.solution {V : ℕ} (a b c : Fin V → ℕ) {m c₀ : ℕ} {B : Finset (Fin V)}
    {i : Fin V → ℕ} {v w : Fin V}
    (hv : v ∈ B) (hiv : i v + 1 = m) (hw : (w : ℕ) = top B + 1) (hiw : i w = 0) (u : Fin V) :
    accT a b c m c₀ (insert w (B.erase v)) (Function.update i v 0) u =
      accT a b c m c₀ B i u + (if u = v then a v + c₀ else 0) + (if u = w then b w else 0) := by

  simp only [accT, done_move hv hw]
  by_cases huv : u = v
  · subst v
    have h1 : ¬((u : ℕ) < top B ∧ u ∉ B) := fun h => h.2 hv
    have huw : u ≠ w := by
      intro h
      have := le_top hv
      rw [h] at this
      omega
    subst m
    simp [h1, hv, huw] <;> ring
  · by_cases huw : u = w
    · subst w
      have hwB : u ∉ B := fun h => by have := le_top h; omega
      have h2 : ¬((u : ℕ) < top B) := by omega
      simp [huv, hwB, h2, hiw, Function.update_apply]
    · by_cases huB : u ∈ B
      · simp [huv, huw, huB, Function.update_apply]
      · simp [huv, huw, huB, Function.update_apply]
end Formalism.G0.WalkSharpP
