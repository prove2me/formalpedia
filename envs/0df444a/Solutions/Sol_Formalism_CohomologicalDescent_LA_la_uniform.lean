-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:34.495906+00:00
-- url     : https://prove2.me/submissions/4ac6e2bb-7f80-4dc0-a9cb-27f952769124

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_dualWeyl_fg
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylRational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ dualWeyl ℤ r n ν, ((N : ℕ) : ℤ) • x ∈ weyl ℤ r n hn ν := by
  classical
  obtain ⟨S, hS⟩ := la_dualWeyl_fg r n ν
  have hc := weylRational r n hn ν hν
  choose! c hc0 hc1 using hc
  have hSm : ∀ g ∈ S, g ∈ dualWeyl ℤ r n ν := fun g hg => hS ▸ Submodule.subset_span hg
  refine ⟨(∏ g ∈ S, c g).natAbs, ?_, ?_⟩
  · rw [Int.natAbs_ne_zero, Finset.prod_ne_zero_iff]
    exact fun g hg => hc0 g (hSm g hg)
  · intro x hx
    have key : (∏ g ∈ S, c g) • x ∈ weyl ℤ r n hn ν := by
      rw [← hS] at hx
      induction hx using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem c hg
        rw [ht, mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (hc1 g (hSm g hg))
      | zero => simp
      | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
    rcases Int.natAbs_eq (∏ g ∈ S, c g) with h | h
    · rw [← h]
      exact key
    · have h2 : (((∏ g ∈ S, c g).natAbs : ℕ) : ℤ) = -(∏ g ∈ S, c g) := by omega
      rw [h2, neg_smul]
      exact Submodule.neg_mem _ key
end Formalism.CohomologicalDescent.LA
