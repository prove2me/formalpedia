-- Prove2me | solution 1 for Formalism.IncomingBounds.thmPExp_degree_le_of_mem_antidiagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:14.923673+00:00
-- url     : https://prove2.me/submissions/0659ad5a-2a3f-4d48-9c0e-5ced3813aa60

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp

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
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds
variable {C : Type} [Field C] {σ : Type}
namespace Formalism.IncomingBounds
theorem _root_.solution [DecidableEq σ] {m : σ →₀ ℕ} {pq : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hpq : pq ∈ antidiagonal m) : pq.1.degree ≤ m.degree ∧ pq.2.degree ≤ m.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  have := congrArg Finsupp.degree hpq
  rw [map_add] at this
  omega
end Formalism.IncomingBounds
