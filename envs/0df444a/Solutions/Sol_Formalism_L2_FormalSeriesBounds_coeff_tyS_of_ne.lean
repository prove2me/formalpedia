-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_tyS_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:18.420899+00:00
-- url     : https://prove2.me/submissions/8562cb1b-7674-470f-aa4d-bbee34200a68

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
omit hl
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (a : ℕ → C) (m : ℕ) (hm : ∀ s, l ^ s ≠ m) : PowerSeries.coeff m (tyS l a) = 0 := by
  unfold tyS
  rw [PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun s _ => if_neg (hm s)
end Formalism.L2.FormalSeriesBounds
