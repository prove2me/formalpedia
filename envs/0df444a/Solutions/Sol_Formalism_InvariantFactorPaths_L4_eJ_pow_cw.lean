-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eJ_pow_cw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:15:55.571607+00:00
-- url     : https://prove2.me/submissions/4dc87b98-a34f-4fb8-a386-22859d78be65

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eW_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_shiftN_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_shiftN_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eJ_cw_lt
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
variable (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Cs : Finset (Fin r)) (th : Fin r → ℤ)
  (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ HWC p LL (K + 1) Cs th)
include hv hx
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (s t : Fin r) (hs : s ∈ Cs) (ht : t ∈ Cs) (hst : s < t) : ∀ (i : ℕ) (γ : Fin r → ℤ),
    ((glAct p LL K s t : Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) ^ i) (cw p K γ x) =
      ((-1 : ℚ_[p]) ^ i) • ((eW p K s t) ^ i) (cw p K (shiftN γ t s i) x) := by
  intro i
  induction i with
  | zero => intro γ; simp [shiftN_zero]
  | succ i ih =>
    intro γ
    rw [pow_succ, Module.End.mul_apply, eJ_cw_lt LL hv Cs th x hx s t hs ht hst γ, map_neg,
      ← Module.End.mul_apply, ((eW_comm LL s t s t).pow_left i).eq, Module.End.mul_apply, ih, shiftN_succ, map_smul,
      ← Module.End.mul_apply, ← pow_succ', pow_succ (-1 : ℚ_[p]), mul_neg_one, neg_smul]
    push_cast
    rfl
end Formalism.InvariantFactorPaths.L4
