-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_F_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:55:15.762077+00:00
-- url     : https://prove2.me/submissions/b368ec57-9818-42fa-93ae-913278af59a2

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_F_F
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_F_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_free_X
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_free_ehP
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_free_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {r' : ℕ} (w' e' : Fin r' → σ) (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (hw : ∀ c, zv ≠ w' c ∧ sv ≠ w' c ∧ (∀ d, w d ≠ w' c) ∧ ∀ d, e d ≠ w' c)
    (he : ∀ c, zv ≠ e' c ∧ sv ≠ e' c ∧ (∀ d, w d ≠ e' c) ∧ ∀ d, e d ≠ e' c) :
    Commute (tieF (k := ℚ_[p]) w' e') (cmTiePL w e zv sv o n z) := by
  unfold cmTiePL
  refine Commute.sum_right _ _ _ (fun l _ => Commute.smul_right ?_ _)
  refine Commute.mul_right (Commute.pow_right ?_ _) (Commute.mul_right (Commute.pow_right (cm_F_F _ _ _ _) _) ?_)
  · exact cm_F_mul w' e' (ehP w e zv sv)
      (fun c => free_ehP (hw c).1 (hw c).2.1 (hw c).2.2.1 (hw c).2.2.2)
      (fun c => free_ehP (he c).1 (he c).2.1 (he c).2.2.1 (he c).2.2.2)
  · exact cm_F_mul w' e' _ (fun c => free_pow (free_X (hw c).1) _) (fun c => free_pow (free_X (he c).1) _)
end Formalism.InvariantFactorPaths.KP.LL
