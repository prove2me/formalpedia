-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.tyS_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:34:15.316747+00:00
-- url     : https://prove2.me/submissions/370b7c68-6cb0-4b0a-9809-b352cba1b70f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem

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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) (a b : ℕ → C) : tyS l (fun s => a s + b s) = tyS l a + tyS l b := by
  ext n
  simp only [tyS, PowerSeries.coeff_mk, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp
end Formalism.L2.FormalSeriesBounds
