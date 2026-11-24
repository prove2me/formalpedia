-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.tyS_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:24.893003+00:00
-- url     : https://prove2.me/submissions/6f484673-a24c-4b12-859f-363761d01d89

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
theorem _root_.solution : tyS l (fun _ => (0 : C)) = 0 := by
  ext m
  unfold tyS
  simp
end Formalism.L2.FormalSeriesBounds
