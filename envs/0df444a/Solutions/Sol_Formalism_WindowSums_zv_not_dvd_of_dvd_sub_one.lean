-- Prove2me | solution 1 for Formalism.WindowSums.zv_not_dvd_of_dvd_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:18.700607+00:00
-- url     : https://prove2.me/submissions/4ffd7d84-a118-4b94-8508-fc8d87e298e6

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
theorem _root_.solution {x : ℤ_[ℓ]} (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1) : ¬ (ℓ : ℤ_[ℓ]) ∣ x := by
  intro h
  have h1 : (ℓ : ℤ_[ℓ]) ∣ 1 := by
    have h2 := dvd_sub h hx
    rwa [sub_sub_cancel] at h2
  exact zv_prime.not_unit (isUnit_of_dvd_one h1)
end Formalism.WindowSums
