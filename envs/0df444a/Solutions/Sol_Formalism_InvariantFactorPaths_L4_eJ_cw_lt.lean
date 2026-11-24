-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eJ_cw_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:30.949133+00:00
-- url     : https://prove2.me/submissions/9e1054d4-4ae1-4968-8556-57b05a173632

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cw_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cw_WD
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
variable (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Cs : Finset (Fin r)) (th : Fin r → ℤ)
  (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ HWC p LL (K + 1) Cs th)
include hv hx
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (s t : Fin r) (hs : s ∈ Cs) (ht : t ∈ Cs) (hst : s < t) (γ : Fin r → ℤ) :
    glAct p LL K s t (cw p K γ x) = -(eW p K s t (cw p K (shiftW γ t s) x)) := by
  have hk := (Submodule.mem_inf.mp hx).2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hk
  have h0 := hk s t ⟨hs, ht, hst⟩
  rw [glAct_succ LL hv] at h0
  have h1 := congrArg (cw p K γ) h0
  rw [map_add, map_zero, cw_glAct, cw_WD] at h1
  exact eq_neg_of_add_eq_zero_left h1
end Formalism.InvariantFactorPaths.L4
