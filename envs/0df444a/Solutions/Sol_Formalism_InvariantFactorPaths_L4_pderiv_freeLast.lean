-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pderiv_freeLast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:44.199883+00:00
-- url     : https://prove2.me/submissions/0989a36c-f682-446b-ad14-b08a4577189e

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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ FreeLast p K r) (d : Fin r) :
    pderiv (Fin.last K, d) x = 0 := by
  rw [FreeLast, MvPolynomial.mem_restrictSupport_iff] at hx
  rw [x.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  have h0 : m (Fin.last K, d) = 0 := hx hm d
  rw [MvPolynomial.pderiv_monomial, h0]
  simp
end Formalism.InvariantFactorPaths.L4
