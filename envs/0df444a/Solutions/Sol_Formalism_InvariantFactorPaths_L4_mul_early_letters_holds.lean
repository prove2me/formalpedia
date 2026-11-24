-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mul_early_letters_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:15.19688+00:00
-- url     : https://prove2.me/submissions/a7f0e2b0-22c4-4d3b-a505-52c9933b7996

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_nil
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_cons
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_criterion_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_X_mul_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_single_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : MulEarly := by
  intro p hp K r hr LL j M c h hj
  have hK : ¬ K < j := by omega
  have hX : ∀ a b : Fin r, ∀ g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      glAct p LL j a b (X (Fin.last K, c) * g) = X (Fin.last K, c) * glAct p LL j a b g := by
    intro a b g
    rw [glAct_mul, glAct_X]
    simp [Fin.val_last, hK]
  have hw : ∀ l : List (Fin r),
      wd p LL j l (X (Fin.last K, c) * h) = X (Fin.last K, c) * wd p LL j l h := by
    intro l
    induction l with
    | nil => simp only [wd_nil]
    | cons d l ih => rw [wd_cons, wd_cons, ih, hX]
  rw [raising_criterion_holds p (K + 1) r LL j M, raising_criterion_holds p (K + 1) r LL j M]
  refine forall_congr' fun l => ?_
  show wd p LL j l (X (Fin.last K, c) * h) ∈ SuppLE p LL j M ↔ wd p LL j l h ∈ SuppLE p LL j M
  rw [hw, X_mul_mem]
  simp [wt_single_add, Fin.val_last, hK]
end Formalism.InvariantFactorPaths.L4
