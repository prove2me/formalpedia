-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.strip_monomial_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:13.109128+00:00
-- url     : https://prove2.me/submissions/e6cb9fbb-10e6-4198-82d7-5206f66fb932

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_coeff_strip
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
theorem _root_.solution (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v = 0) :
    strip p v e (monomial (Finsupp.single v e + m) 1) = monomial m 1 := by
  classical
  ext n
  rw [coeff_strip, coeff_monomial, coeff_monomial]
  by_cases h1 : n v = 0
  · rw [if_pos h1]
    by_cases h2 : m = n
    · subst h2
      simp
    · rw [if_neg h2, if_neg]
      intro h3
      exact h2 (add_left_cancel h3)
  · rw [if_neg h1, if_neg]
    rintro rfl
    exact h1 hm
end Formalism.InvariantFactorPaths.L4
