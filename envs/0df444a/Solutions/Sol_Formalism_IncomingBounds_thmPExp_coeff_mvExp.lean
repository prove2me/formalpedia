-- Prove2me | solution 1 for Formalism.IncomingBounds.thmPExp_coeff_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:57.31543+00:00
-- url     : https://prove2.me/submissions/a3fca98f-037f-4fd8-8272-d1b6d6a462fb

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Theorems.Thm_Formalism_IncomingBounds_thmPExp_coeff_pow_eq_zero

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
theorem _root_.solution {h : MvPowerSeries σ C} (hh : constantCoeff h = 0)
    (m : σ →₀ ℕ) {N : ℕ} (hN : m.degree < N) :
    coeff m (mvExp h) = ∑ k ∈ range N, coeff m (h ^ k) / (k.factorial : C) := by
  change ∑ k ∈ range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) = _
  apply Finset.sum_subset (range_subset_range.2 (by omega))
  intro k hk hk'
  simp only [mem_range, not_lt] at hk hk'
  rw [thmPExp_coeff_pow_eq_zero hh (by omega), zero_div]
end Formalism.IncomingBounds
