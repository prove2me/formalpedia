-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pol_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:39.500998+00:00
-- url     : https://prove2.me/submissions/e72f9d35-d52b-427f-b90b-24c27da2af0d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_mul_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_multiDeg_pow
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last K)) (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ Pol p r LL ↔ h ∈ Pol p r (setLast LL (LL.deg (Fin.last K) - e)) := by
  unfold Pol
  rw [pow_mul_mem]
  have hset : {m | Finsupp.single (Fin.last K, ρ) e + m ∈ {m | MultiDeg LL m}} =
      {m | MultiDeg (setLast LL (LL.deg (Fin.last K) - e)) m} := by
    ext m
    simp only [Set.mem_setOf_eq]
    exact multiDeg_pow LL ρ e he m
  rw [hset]
end Formalism.InvariantFactorPaths.L4
