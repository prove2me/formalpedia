-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_dom_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:44:40.118173+00:00
-- url     : https://prove2.me/submissions/cd94a839-2e32-4b6f-af86-ae6654906539

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {lam kap : Fin n → ℤ} {b : ℕ} (hk : Dominant kap) (hs : HStrip lam kap b) : Dominant lam := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have h1 : x.1 + 1 < n := by have := y.2; have := Fin.lt_def.1 hlt; omega
    have h2 := hs.2.1 x h1
    have h4 : kap y ≤ kap ⟨x.1 + 1, h1⟩ := hk (by
      apply Fin.le_def.2; have := Fin.lt_def.1 hlt; simp only; omega)
    exact (hs.1 y).trans (h4.trans h2)
end Formalism.InvariantFactorPaths.ColumnFamilies
