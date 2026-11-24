-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.hWC_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:11:48.988033+00:00
-- url     : https://prove2.me/submissions/e5f2eb69-2f22-4eda-9046-8369228cefd9

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_setLast
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtSpC_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_pow
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
theorem _root_.solution (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (e o : ℕ) (w : Fin r → ℤ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ HWC p LL (K + 1) (univ.erase ρ) w ↔
      h ∈ HWC p (setLast LL o) (K + 1) (univ.erase ρ) (shiftWt w ρ e) := by
  simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, wtSpC_pow LL hv ρ e o,
    glAct_setLast]
  refine and_congr Iff.rfl (forall_congr' fun c => forall_congr' fun d => forall_congr' fun hcd => ?_)
  rw [glAct_pow LL hv ρ c d (Finset.ne_of_mem_erase hcd.2.1) e h]
  constructor
  · intro h0
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (X_ne_zero _))
  · intro h0
    rw [h0, mul_zero]
end Formalism.InvariantFactorPaths.L4
