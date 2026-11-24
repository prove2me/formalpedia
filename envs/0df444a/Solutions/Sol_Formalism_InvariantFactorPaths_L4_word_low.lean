-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.word_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:48.337713+00:00
-- url     : https://prove2.me/submissions/a60e9879-7d78-469e-947c-ae2b6b8365b6

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_nil
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_snoc
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_low_keep
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_comm


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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (l : List (Fin r)) :
    ∀ a b : Fin r, a ≠ 0 → ∀ G : MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ l', wd p LL j l' G ∈ SuppLE p LL j M) → wd p LL j l (glAct p LL j a b G) ∈ SuppLE p LL j M := by
  induction l using List.reverseRecOn with
  | nil =>
    intro a b ha G hG
    rw [wd_nil]
    exact low_keep p LL j a b ha M G (by simpa [wd_nil] using hG [])
  | append_singleton l c ih =>
    intro a b ha G hG
    rw [wd_snoc]
    have hc := glAct_comm (p := p) LL j 0 c a b G
    have heq : glAct p LL j 0 c (glAct p LL j a b G) = glAct p LL j a b (glAct p LL j 0 c G) +
        ((if c = a then glAct p LL j 0 b G else 0) - (if b = 0 then glAct p LL j a c G else 0)) := by
      rw [← hc]; abel
    rw [heq, map_add, map_sub]
    refine Submodule.add_mem _ ?_ (Submodule.sub_mem _ ?_ ?_)
    · exact ih a b ha _ (fun l' => by rw [← wd_snoc]; exact hG _)
    · split_ifs
      · rw [← wd_snoc]; exact hG _
      · rw [map_zero]; exact Submodule.zero_mem _
    · split_ifs
      · exact ih a c ha G hG
      · rw [map_zero]; exact Submodule.zero_mem _
end Formalism.InvariantFactorPaths.L4
