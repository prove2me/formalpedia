-- Prove2me | solution 1 for Formalism.IncomingBounds.thmPExp_coeff_pow_mul_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:13.99686+00:00
-- url     : https://prove2.me/submissions/9fa914e6-1f7b-49fd-8da8-745338247720

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
theorem _root_.solution {a b : MvPowerSeries σ C} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) {m : σ →₀ ℕ} {j j' : ℕ} (hk : m.degree < j + j') :
    coeff m (a ^ j * b ^ j') = 0 :=
  by
  have h1 := le_order_pow_of_constantCoeff_eq_zero j ha
  have h2 := le_order_pow_of_constantCoeff_eq_zero j' hb
  apply coeff_of_lt_order
  calc ((m.degree : ℕ) : ℕ∞) < ((j + j' : ℕ) : ℕ∞) := by exact_mod_cast hk
    _ = (j : ℕ∞) + (j' : ℕ∞) := by push_cast; rfl
    _ ≤ (a ^ j).order + (b ^ j').order := add_le_add h1 h2
    _ ≤ _ := le_order_mul
end Formalism.IncomingBounds
