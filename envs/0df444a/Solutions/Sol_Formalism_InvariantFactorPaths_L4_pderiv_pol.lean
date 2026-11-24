-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pderiv_pol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:47.696531+00:00
-- url     : https://prove2.me/submissions/cb8b8fcd-09d4-4195-ae7d-c80d809b8429

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_multiDeg_pow
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (a : Fin r) (o : ℕ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : x ∈ Pol p r (setLast LL (o + 1))) : pderiv (Fin.last K, a) x ∈ Pol p r (setLast LL o) := by
  classical
  have e : setLast (setLast LL (o + 1)) ((setLast LL (o + 1)).deg (Fin.last K) - 1) = setLast LL o := by
    simp [setLast]
  rw [Pol, mem_restrictSupport_iff] at hx ⊢
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, coeff_pderiv] at hm
  have h1 : m + Finsupp.single (Fin.last K, a) 1 ∈ x.support := mem_support_iff.mpr (left_ne_zero_of_mul hm)
  have h2 : MultiDeg (setLast LL (o + 1)) (m + Finsupp.single (Fin.last K, a) 1) := hx (Finset.mem_coe.mpr h1)
  rw [add_comm m, multiDeg_pow (setLast LL (o + 1)) a 1 (by simp [setLast]) m, e] at h2
  exact h2
end Formalism.InvariantFactorPaths.L4
