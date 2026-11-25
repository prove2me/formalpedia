-- Prove2me | solution 1 for Formalism.IncomingBounds.thmPExp_coeff_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:26.099245+00:00
-- url     : https://prove2.me/submissions/d0a4c4e7-2f80-48a2-aae7-f60deb4a1361

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
theorem _root_.solution {h : MvPowerSeries σ C} (hh : constantCoeff h = 0)
    {m : σ →₀ ℕ} {k : ℕ} (hk : m.degree < k) : coeff m (h ^ k) = 0 :=
  coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hk)
    (le_order_pow_of_constantCoeff_eq_zero k hh))
end Formalism.IncomingBounds
