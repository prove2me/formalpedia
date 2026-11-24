-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eul_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:19.669498+00:00
-- url     : https://prove2.me/submissions/cfe520e5-5cc5-4ed4-8a94-9c5c45813a9d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_GM_ProjS_eulL_of_support
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (o : ℕ) (a : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hP : x ∈ Pol p r (setLast LL (o + 1))) :
    ProjS.eulL (fun c : Fin r => (Fin.last K, c)) (pderiv (Fin.last K, a) x) =
      ((o : ℕ) : ℚ_[p]) • pderiv (Fin.last K, a) x := by
  classical
  refine ProjS.eulL_of_support _ _ _ ?_
  intro m hm
  rw [mem_support_iff, coeff_pderiv] at hm
  rw [Pol, mem_restrictSupport_iff] at hP
  have h1 := hP (Finset.mem_coe.mpr (mem_support_iff.mpr (left_ne_zero_of_mul hm))) (Fin.last K)
  have h2 : (setLast LL (o + 1)).deg (Fin.last K) = o + 1 := by simp [setLast]
  rw [h2] at h1
  simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h1
  have h3 : ∑ c : Fin r, (Finsupp.single ((Fin.last K, a) : Fin (K + 1) × Fin r) 1) (Fin.last K, c) = 1 := by
    simp [Finsupp.single_apply, Prod.ext_iff]
  omega
end Formalism.InvariantFactorPaths.L4
