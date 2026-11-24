-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glAct_X_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:49:13.969224+00:00
-- url     : https://prove2.me/submissions/be2d57d8-90e4-4f77-b5f4-2d795aa77f6d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_X_mul_int_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (c : Fin r) (v : Fin N × Fin r) (g : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hg : g ∈ IntPol p (Fin N × Fin r)) : glAct p LL j 0 c (X v) * g ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨i, c'⟩ := v
  rw [glAct_X]
  split_ifs
  · exact (X_mul_int_iff _ _).2 hg
  · rw [zero_mul]; exact Submodule.zero_mem _
  · rw [neg_mul]; exact Submodule.neg_mem _ ((X_mul_int_iff _ _).2 hg)
  · rw [zero_mul]; exact Submodule.zero_mem _
  · rw [zero_mul]; exact Submodule.zero_mem _
end Formalism.InvariantFactorPaths.L4
