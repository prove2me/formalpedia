-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.initPart_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:49:15.018055+00:00
-- url     : https://prove2.me/submissions/ed5da2df-f062-4f57-b0f3-2a7e06f9e46c

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (v : σ) (e : ℕ) (h : MvPolynomial σ ℚ_[p]) :
    initPart v e (X v ^ e * h) = X v ^ e * initPart v 0 h := by
  classical
  have c1 : ∀ (m : σ →₀ ℕ) (g' : MvPolynomial σ ℚ_[p]), coeff m (X v ^ e * g') =
      if e ≤ m v then coeff (m - Finsupp.single v e) g' else 0 := by
    intro m g'
    rw [X_pow_eq_monomial, coeff_monomial_mul']
    simp only [Finsupp.single_le_iff, one_mul]
  ext m
  rw [coeff_initPart, c1, c1, coeff_initPart]
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
  split_ifs <;> first | rfl | omega | (exfalso; omega)
end Formalism.InvariantFactorPaths.L4
