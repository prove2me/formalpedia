-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.self_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:59.02127+00:00
-- url     : https://prove2.me/submissions/eebd96fa-9449-45d4-aa40-fec58b3b4316

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundUnconditionalOfSat
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundPosOfProjSat
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_of_free


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hF : x ∈ FreeOf p (Fin.last K, ρ))
    (hY : x ∈ Y p LL J M) (hi : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ 0) • x := by
  refine ⟨x, hY, hi, ?_⟩
  rw [pow_zero, one_smul, ← resL_apply, resL_of_free _ x hF]
end Formalism.InvariantFactorPaths.L4
