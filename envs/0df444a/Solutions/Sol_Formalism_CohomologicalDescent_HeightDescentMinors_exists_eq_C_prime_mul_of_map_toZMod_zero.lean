-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.exists_eq_C_prime_mul_of_map_toZMod_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:54.233442+00:00
-- url     : https://prove2.me/submissions/5ec6e4f7-fc2d-4f97-88d8-b2d63b2d1a75

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (g : ℤ_[l]⟦X⟧)
    (h : PowerSeries.map (PadicInt.toZMod (p := l)) g = 0) : ∃ r, g = C (l : ℤ_[l]) * r := by
  have h0 : ∀ n, ∃ r, coeff n g = (l : ℤ_[l]) * r := by
    intro n
    have h1 : PadicInt.toZMod (coeff n g) = 0 := by
      have := congrArg (coeff n) h
      simpa using this
    have h2 : coeff n g ∈ RingHom.ker (PadicInt.toZMod (p := l)) := h1
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2
    exact h2
  choose r hr using h0
  exact ⟨PowerSeries.mk r, by ext n; rw [coeff_C_mul, coeff_mk, hr n]⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
