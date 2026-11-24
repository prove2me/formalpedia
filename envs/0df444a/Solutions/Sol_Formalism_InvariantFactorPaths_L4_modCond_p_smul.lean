-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.modCond_p_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:47.306257+00:00
-- url     : https://prove2.me/submissions/86064428-a2da-4776-9db2-55fe308a1837

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dw_int
import Theorems.Thm_Formalism_CountingSumsFrames_intPol_norm


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
variable (M : WithTop ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (b : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hb : b ∈ IntPol p (Fin N × Fin r)) :
    ModCond p LL j M ((p : ℚ_[p]) • b) := by
  intro l hl m _
  rw [map_smul, coeff_smul, smul_eq_mul, norm_mul]
  have h1 := intPol_norm _ (dw_int p LL j l hl b hb) m
  calc ‖(p : ℚ_[p])‖ * ‖coeff m (dw p LL j l b)‖ ≤ ‖(p : ℚ_[p])‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact Padic.norm_p_lt_one
end Formalism.InvariantFactorPaths.L4
