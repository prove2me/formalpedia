-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_incl_of_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:39.438587+00:00
-- url     : https://prove2.me/submissions/1dfe42f6-0870-42ce-8d23-9a7ed758e3e9

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_dualWeyl_fg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l e : ℕ) (hl : l.Prime)
    (h : ∀ g ∈ dualWeyl ℤ r n ν, ∃ m : ℕ, ¬ l ∣ m ∧
      ((m * l ^ e : ℕ) : ℤ) • g ∈ weyl ℤ r n hn ν) : InclZ r n hn ν l e := by
  obtain ⟨S, hS⟩ := la_dualWeyl_fg r n ν
  choose! M hM hMw using h
  have hS' : ∀ g ∈ S, g ∈ dualWeyl ℤ r n ν := by
    intro g hg
    rw [← hS]
    exact Submodule.subset_span hg
  unfold InclZ
  refine ⟨∏ g ∈ S, M g, ?_, fun x hx => ?_⟩
  · rw [Prime.dvd_finset_prod_iff hl.prime]
    push_neg
    exact fun g hg => hM g (hS' g hg)
  · rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨K, hK⟩ := Finset.dvd_prod_of_mem M hg
      rw [hK, show M g * K * l ^ e = K * (M g * l ^ e) by ring, Nat.cast_mul, mul_smul]
      exact Submodule.smul_mem _ _ (hMw g (hS' g hg))
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ a hx
end Formalism.CohomologicalDescent.LA
