-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.resL_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:45.72174+00:00
-- url     : https://prove2.me/submissions/f6568b97-e49b-453f-9b69-ca0ed703177d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (v u : σ) (huv : u ≠ v) (e : ℕ) (g : MvPolynomial σ ℚ_[p]) :
    resL p v e (pderiv u g) = pderiv u (resL p v e g) := by
  classical
  have hr : ∀ y, resL p v e y = initPart v e y := fun _ => rfl
  have hi : ∀ (m : σ →₀ ℕ) (a : ℚ_[p]),
      initPart v e (monomial m a) = if m v = e then monomial m a else 0 := by
    intro m a
    by_cases ha : a = 0
    · subst ha
      simp [initPart]
    · rw [initPart, MvPolynomial.support_monomial, if_neg ha, Finset.sum_singleton,
        MvPolynomial.coeff_monomial, if_pos rfl]
  induction g using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [hr, hr, MvPolynomial.pderiv_monomial, hi, hi]
    have hmv : (m - Finsupp.single u 1 : σ →₀ ℕ) v = m v := by
      simp [Finsupp.single_apply, huv]
    rw [hmv]
    split_ifs <;> simp [MvPolynomial.pderiv_monomial]
  | add f g hf hg =>
    simp only [map_add, hf, hg]
end Formalism.InvariantFactorPaths.L4
