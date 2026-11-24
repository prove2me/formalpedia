-- Prove2me | solution 1 for Formalism.WindowSums.zv_emult_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:11.470806+00:00
-- url     : https://prove2.me/submissions/e699f969-f95a-4d4a-a7b5-979a00943919

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
theorem _root_.solution {c : ℤ_[ℓ]} (hc : IsUnit c) (y : ℤ_[ℓ]) :
    emultiplicity (ℓ : ℤ_[ℓ]) (c * y) = emultiplicity (ℓ : ℤ_[ℓ]) y := by
  rw [emultiplicity_mul zv_prime, emultiplicity_of_isUnit_right zv_prime.not_unit hc, zero_add]
end Formalism.WindowSums
