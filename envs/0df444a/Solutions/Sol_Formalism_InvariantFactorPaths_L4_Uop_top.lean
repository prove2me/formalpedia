-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.Uop_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:15.945576+00:00
-- url     : https://prove2.me/submissions/bac6833d-e342-4836-9da6-fd47f7cd99ef

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_apply
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_succ
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
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : ℤ)
    (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (h0 : glAct p LL (K + 1) 0 0 G = ((c : ℤ) : ℚ_[p]) • G)
    (hb : ∀ b : Fin r, b ≠ 0 → glAct p LL (K + 1) 0 b G = 0) : Uop p LL c univ 0 G = 0 := by
  rw [Uop_apply]
  have e : ∀ b, glAct p LL K 0 b G =
      glAct p LL (K + 1) 0 b G - X (Fin.last K, 0) * pderiv (Fin.last K, b) G := by
    intro b; rw [glAct_succ LL hv]; abel
  simp only [e, mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ b, X (Fin.last K, b) * glAct p LL (K + 1) 0 b G = X (Fin.last K, 0) * (((c : ℤ) : ℚ_[p]) • G) := by
    rw [Finset.sum_eq_single 0, h0]
    · intro b _ hb'; rw [hb b hb', mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : ∑ b, X (Fin.last K, b) * (X (Fin.last K, 0) * pderiv (Fin.last K, b) G) =
      X (Fin.last K, 0) * ProjS.eulL (fun c : Fin r => (Fin.last K, c)) G := by
    rw [ProjS.eulL_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h1, h2]
  abel
end Formalism.InvariantFactorPaths.L4
