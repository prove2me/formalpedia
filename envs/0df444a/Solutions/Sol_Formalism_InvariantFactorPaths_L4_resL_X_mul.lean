-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.resL_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:45.488195+00:00
-- url     : https://prove2.me/submissions/f3f812fd-58c2-4c65-b651-acb90d33dbe9

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
    resL p v e (X u * g) = X u * resL p v e g := by
  classical
  ext m
  change (initPart v e (X u * g)).coeff m = (X u * initPart v e g).coeff m
  rw [coeff_initPart, MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_mul']
  by_cases hu : u ∈ m.support
  · have hmv : (m - Finsupp.single u 1 : σ →₀ ℕ) v = m v := by
      simp [Finsupp.single_apply, huv]
    simp only [hu, if_true, coeff_initPart, hmv]
  · simp only [hu, if_false]
    split_ifs <;> rfl
end Formalism.InvariantFactorPaths.L4
