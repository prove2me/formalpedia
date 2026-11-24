-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.sSYTExists_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:05.37989+00:00
-- url     : https://prove2.me/submissions/63c15ea0-f680-4d75-a4df-2df0857ef4d5

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SSYTExists
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcssyt_bidetExp_cons
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcssyt_consI_strictMono
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcssyt_shapeDeg_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Finset
noncomputable section
namespace Formalism.GradedWeylDivisibility
private theorem exists_tableau_of_sum_eq_lemma (hP : SSYTPeel) (r n : ℕ) :
    ∀ (N : ℕ) (ν : Fin n → ℕ) (m : Fin r × Fin n →₀ ℕ), ∑ t, ν t = N →
      (∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) → Interlaced m →
      ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
        shapeDeg sz = ν ∧ (∀ k, StrictMono (I k)) ∧ bidetExp sz hsz I = m := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih ν m hN hcol hint_r
  by_cases hm : m = 0
  · subst hm
    have hν : ν = 0 := by
      funext t
      rw [← hcol t]
      simp
    subst hν
    refine ⟨0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, ?_, fun k => k.elim0, ?_⟩
    · funext t
      simp [shapeDeg]
    · simp [bidetExp]
  · obtain ⟨h, hh, c, hc, hν, hle, hint', hcol'⟩ := hP r n ν m hcol hint_r hm
    obtain ⟨⟨a0, t0⟩, hne⟩ : ∃ x, m x ≠ 0 := by
      by_contra H
      push_neg at H
      exact hm (Finsupp.ext H)
    have hpos : 0 < ν t0 := by
      rw [← hcol t0]
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero hne)
        (Finset.single_le_sum (f := fun a => m (a, t0)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a0))
    have hlt : ∑ t, (ν t - if t.val < h then 1 else 0) < N := by
      rw [← hN]
      apply Finset.sum_lt_sum
      · intro t _
        exact Nat.sub_le _ _
      · refine ⟨t0, Finset.mem_univ _, ?_⟩
        rw [if_pos ((hν t0).2 hpos)]
        omega
    obtain ⟨K, sz, hsz, I, hshape, hI, hexp⟩ :=
      ih _ hlt (fun t => ν t - if t.val < h then 1 else 0) (m - colExp c hh) rfl hcol' hint'
    refine ⟨K + 1, Fin.cons h sz, lcssyt_consSz hh sz hsz, lcssyt_consI sz c I, ?_,
      lcssyt_consI_strictMono sz c I hc hI, ?_⟩
    · funext t
      rw [lcssyt_shapeDeg_cons, congrFun hshape t]
      by_cases ht : t.val < h
      · have h1 := (hν t).1 ht
        simp only [if_pos ht]
        omega
      · simp only [if_neg ht]
        omega
    · rw [lcssyt_bidetExp_cons hh c sz hsz I, hexp]
      exact add_tsub_cancel_of_le hle
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (hP : SSYTPeel) : SSYTExists :=
  fun r n ν m hcol hint_r => exists_tableau_of_sum_eq_lemma hP r n _ ν m rfl hcol hint_r
end Formalism.GradedWeylDivisibility
