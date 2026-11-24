-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_tyS_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:08.629813+00:00
-- url     : https://prove2.me/submissions/cb9f9a71-7f33-4c0d-9737-7fde95647425

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {l : ℕ} (hl : 2 ≤ l)
include hl
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (a : ℕ → C) (s : ℕ) : PowerSeries.coeff (l ^ s) (tyS l a) = a s := by
  unfold tyS
  rw [PowerSeries.coeff_mk]
  have hinj : ∀ t, l ^ t = l ^ s ↔ t = s := fun t => (Nat.pow_right_injective hl).eq_iff
  simp only [hinj]
  rw [Finset.sum_ite_eq', if_pos]
  have hs : s < l ^ s := Nat.lt_pow_self (by omega)
  exact Finset.mem_range.2 (by omega)
end Formalism.L2.FormalSeriesBounds
