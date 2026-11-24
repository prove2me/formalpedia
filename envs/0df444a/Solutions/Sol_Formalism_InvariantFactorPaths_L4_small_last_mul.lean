-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.small_last_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:49.682809+00:00
-- url     : https://prove2.me/submissions/950ccd4d-8a2e-408c-a62f-394fbe4e8862

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_wt
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_withTop_shift


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
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c' : Fin r)
    (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hg : ∀ m : Fin (K + 1) × Fin r →₀ ℕ, ¬ (((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M + ((-1 : ℤ) : WithTop ℤ)) →
      ‖coeff m g‖ < 1) :
    ∀ m : Fin (K + 1) × Fin r →₀ ℕ, ¬ (((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M) →
      ‖coeff m (X (Fin.last K, c') * g)‖ < 1 := by
  classical
  intro m hm
  rw [coeff_X_mul']
  split_ifs with hs
  · apply hg
    intro hle
    apply hm
    have e : Finsupp.single (Fin.last K, c') 1 + (m - Finsupp.single (Fin.last K, c') 1) = m :=
      add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr
        (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)))
    rw [← e, last_wt LL j hj hv]
    rw [← withTop_shift] at hle
    refine le_trans ?_ hle
    exact_mod_cast (by split_ifs <;> omega)
  · rw [norm_zero]; exact one_pos
end Formalism.InvariantFactorPaths.L4
