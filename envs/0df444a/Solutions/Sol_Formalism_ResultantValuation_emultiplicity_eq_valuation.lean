-- Prove2me | solution 1 for Formalism.ResultantValuation.emultiplicity_eq_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:48.015092+00:00
-- url     : https://prove2.me/submissions/ae0e23a2-1053-414f-a413-ec18df0870ec

import Mathlib
import Definitions.Def_Formalism_ResultantValuation_WindowValuation
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Window
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.ResultantValuation
section Padic
variable {l : ℕ} [Fact l.Prime]
private theorem pow_dvd_iff_le_valuation_lemma {x : ℤ_[l]} (hx : x ≠ 0) (n : ℕ) :
    (l : ℤ_[l]) ^ n ∣ x ↔ n ≤ x.valuation := by
  simpa [Ideal.mem_span_singleton] using PadicInt.mem_span_pow_iff_le_valuation x hx n
end Padic
end Formalism.ResultantValuation
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.ResultantValuation
variable {l : ℕ} [Fact l.Prime]
namespace Formalism.ResultantValuation
theorem _root_.solution {x : ℤ_[l]} (hx : x ≠ 0) :
    emultiplicity (l : ℤ_[l]) x = (x.valuation : ℕ∞) := by
  rw [emultiplicity_eq_coe]
  refine ⟨(pow_dvd_iff_le_valuation_lemma hx _).2 le_rfl, fun h => ?_⟩
  have h1 := (pow_dvd_iff_le_valuation_lemma hx _).1 h
  omega
end Formalism.ResultantValuation
