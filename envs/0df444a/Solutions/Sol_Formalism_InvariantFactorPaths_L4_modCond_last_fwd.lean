-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.modCond_last_fwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:11:50.487132+00:00
-- url     : https://prove2.me/submissions/953bf623-5a57-4a51-8c34-84ab2b2db9eb

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_succ_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_sq_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_of_stable
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_small
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_dpow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_add
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_small_last_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_X


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
    (g g' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hg : ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g) (hg' : ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g') :
    ModCond p LL j M (X (Fin.last K, c') * g + X (Fin.last K, (0 : Fin r)) * g') := by
  refine modCond_of_stable p LL j M {f | ∃ g g' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
    ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g ∧ ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g' ∧
      f = X (Fin.last K, c') * g + X (Fin.last K, (0 : Fin r)) * g'} ?_ ?_ _ ⟨g, g', hg, hg', rfl⟩
  · rintro x ⟨g, g', hg, hg', rfl⟩ a ha k
    cases k with
    | zero => rw [dpow_zero]; exact ⟨g, g', hg, hg', rfl⟩
    | succ k =>
      refine ⟨dpow p LL j a (k + 1) g, (if a = c' then dpow p LL j a k g else 0) + dpow p LL j a (k + 1) g',
        modCond_dpow p LL j _ _ hg a ha _, modCond_add p LL j _ _ _ ?_ (modCond_dpow p LL j _ _ hg' a ha _), ?_⟩
      · split_ifs
        · exact modCond_dpow p LL j _ _ hg a ha _
        · exact modCond_zero p LL j _
      · rw [map_add, dpow_succ_mul p LL j a _ _ (glAct_sq_X p LL j a ha _),
          dpow_succ_mul p LL j a _ _ (glAct_sq_X p LL j a ha _), last_X p LL j hj hv, last_X p LL j hj hv, if_neg ha]
        split_ifs <;> ring
  · rintro x ⟨g, g', hg, hg', rfl⟩ m hm
    rw [coeff_add]
    exact lt_of_le_of_lt (Padic.nonarchimedean _ _)
      (max_lt (small_last_mul p LL j M hj hv _ _ (modCond_small p LL j _ _ hg) m hm)
        (small_last_mul p LL j M hj hv _ _ (modCond_small p LL j _ _ hg') m hm))
end Formalism.InvariantFactorPaths.L4
