-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.raising_criterion_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:41:52.746132+00:00
-- url     : https://prove2.me/submissions/3c8d5bcc-6996-4437-a14e-a03b0bffa799

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_nil
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_snoc
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_word_low
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_le_supp


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
theorem _root_.solution : FirstCoordinateRaisingCriterion := by
  intro p hp N r hr LL j M F
  constructor
  · intro hF l
    have hy : ∀ l : List (Fin r), ((l.map fun c => glAct p LL j 0 c).prod) F ∈ YCond p LL j M := by
      intro l
      induction l with
      | nil => simpa using hF
      | cons c l ih =>
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
        exact ycond_glStable (p := p) LL j M 0 c _ ih
    exact ycond_le_supp (p := p) LL j M (hy l)
  · intro hF
    have hS : F ∈ ⨅ l : List (Fin r), (SuppLE p LL j M).comap (wd p LL j l) :=
      (Submodule.mem_iInf _).mpr fun l => hF l
    have hle : (⨅ l : List (Fin r), (SuppLE p LL j M).comap (wd p LL j l)) ≤ YCond p LL j M := by
      unfold YCond
      refine le_sSup ⟨?_, ?_⟩
      · intro x hx
        have := (Submodule.mem_iInf _).mp hx []
        rw [Submodule.mem_comap, wd_nil] at this
        exact this
      · intro c d x hx
        rw [Submodule.mem_iInf] at hx ⊢
        intro l
        rw [Submodule.mem_comap]
        by_cases hc : c = 0
        · subst hc; rw [← wd_snoc]; exact hx _
        · exact word_low p LL j M l c d hc x (fun l' => hx l')
    exact hle hS
end Formalism.InvariantFactorPaths.L4
