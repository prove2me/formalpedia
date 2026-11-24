-- Prove2me | solution 1 for Formalism.WindowSums.zv_not_dvd_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:12.74032+00:00
-- url     : https://prove2.me/submissions/f6d12289-4a15-4531-be7d-39f8cf825a86

import Definitions.Def_Formalism_WindowSums_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal

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
theorem _root_.solution {m : ℕ} (hm : ¬ ℓ ∣ m) : ¬ (ℓ : ℤ_[ℓ]) ∣ (m : ℤ_[ℓ]) := by
  intro h
  rw [← PadicInt.norm_lt_one_iff_dvd] at h
  have h' : ‖((m : ℤ) : ℤ_[ℓ])‖ < 1 := by
    rw [Int.cast_natCast]
    exact h
  exact hm (Int.natCast_dvd_natCast.1 ((PadicInt.norm_int_lt_one_iff_dvd (m : ℤ)).1 h'))
end Formalism.WindowSums
