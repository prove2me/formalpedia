-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_Fpow_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:17.069693+00:00
-- url     : https://prove2.me/submissions/1cdd6bbb-f8dd-4239-ada8-1659ca6d6c06

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_tiePL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_F_P

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
    (he : ∀ c, zv ≠ e' c ∧ sv ≠ e' c ∧ (∀ d, w d ≠ e' c) ∧ ∀ d, e d ≠ e' c) (m : ℕ)
    (x : MvPolynomial σ ℚ_[p]) :
    (tieF w' e' ^ m) (tieP w e zv sv o n z x) = tieP w e zv sv o n z ((tieF w' e' ^ m) x) := by
  have h := (cm_F_P (p := p) w' e' w e zv sv o n z hw he).pow_left m
  have h2 := LinearMap.congr_fun h.eq x
  simpa only [Module.End.mul_apply, cm_tiePL_apply] using h2
end Formalism.InvariantFactorPaths.KP.LL
