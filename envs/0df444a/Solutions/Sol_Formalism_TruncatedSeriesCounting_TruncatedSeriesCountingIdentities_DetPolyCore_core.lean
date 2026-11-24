-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:39:24.99798+00:00
-- url     : https://prove2.me/submissions/43dce612-ffd3-496b-ae93-1803568b97e7

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_allD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
variable {R : Type*} [CommRing R] {G : Type*} [Monoid G] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
theorem _root_.solution {S : Subring R} (ρ : G →* Matrix n n R)
    (hS : ∀ g k, (Matrix.charpolyRev (ρ g)).coeff k ∈ S)
    (l : List (R × ℕ × G)) (hl : ∀ L ∈ l, L.1 ∈ S ∧ 1 ≤ L.2.1) (k : ℕ) : (F ρ l).coeff k ∈ S := by
  have h := allD k ρ hS (k + 1) 1 le_rfl (by omega) l hl
  obtain ⟨q, hq, hqe⟩ := Subring.mem_map.1 h
  have hmem : F ρ l - q ∈ Ideal.span {(X : R[X]) ^ (k + 1)} := by
    rw [← Ideal.Quotient.eq]; exact hqe.symm
  obtain ⟨h', hh'⟩ := Ideal.mem_span_singleton'.1 hmem
  have e : (F ρ l - q).coeff k = 0 := by
    rw [← hh', Polynomial.coeff_mul_X_pow', if_neg (by omega)]
  rw [Polynomial.coeff_sub, sub_eq_zero] at e
  rw [e]
  exact hq k
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
