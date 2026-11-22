-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.accT_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:52.661999+00:00
-- url     : https://prove2.me/submissions/f7214283-be2e-4789-9f3e-689003588e1a

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
    {i : Fin V → ℕ} (hi : ∀ u ∈ B, i u < m) (u : Fin V) :
    accT a b c m c₀ B i u ≤ a u + b u + (m - 1) * c u + m * c₀ := by

  simp only [accT]
  split_ifs with h1 h2
  · exact le_rfl
  · have := hi u h2
    have e1 : i u * c u ≤ (m - 1) * c u := Nat.mul_le_mul_right _ (by omega)
    have e2 : i u * c₀ ≤ m * c₀ := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_add]
    omega
  · exact Nat.zero_le _
end Formalism.G0.WalkSharpP
