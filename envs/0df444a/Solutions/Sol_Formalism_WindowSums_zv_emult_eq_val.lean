-- Prove2me | solution 1 for Formalism.WindowSums.zv_emult_eq_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:10.666832+00:00
-- url     : https://prove2.me/submissions/af369f97-50ba-44cd-9a1a-efc9949fcb80

import Definitions.Def_Formalism_WindowSums_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Theorems.Thm_Formalism_WindowSums_zv_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.WindowSums
open Finset
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
namespace Formalism.WindowSums
theorem _root_.solution {x : ℤ_[ℓ]} (hx : x ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) x = (x.valuation : ℕ∞) := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [emultiplicity_mul zv_prime, emultiplicity_of_isUnit_right zv_prime.not_unit (Units.isUnit _),
    zero_add, emultiplicity_pow_self_of_prime zv_prime]
end Formalism.WindowSums
