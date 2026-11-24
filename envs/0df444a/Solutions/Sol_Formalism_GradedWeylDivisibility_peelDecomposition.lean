-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.peelDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:01.511515+00:00
-- url     : https://prove2.me/submissions/6c128d58-75bc-42b0-a1f8-548797d80e3c

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCpeelLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_PeelDecomp
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcpeel_weight_apply


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
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : PeelDecomp := by
  intro B _ r n l j hlj a0 ω g hg
  have key : ∀ m ∈ g.support, m (a0, l) + m (a0, j) = ω (a0, l) := by
    intro m hm
    have hw := hg (mem_support_iff.1 hm)
    have := lcpeel_weight_apply l j hlj m a0 l
    rw [hw] at this
    simpa using this.symm
  have hterm : ∀ k, X (a0, l) ^ k * X (a0, j) ^ (ω (a0, l) - k) * peel l j a0 k g =
      ∑ m ∈ g.support.filter (fun m => m (a0, l) = k), monomial m (coeff m g) := by
    intro k
    unfold peel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    have hkey := key m hm1
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, monomial_mul, one_mul, one_mul]
    refine congrArg (fun e => monomial e (coeff m g)) ?_
    ext ⟨b, t⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply, Prod.mk.injEq]
    rcases eq_or_ne b a0 with rfl | hb
    · rcases eq_or_ne t l with rfl | ht
      · simp only [hlj, hlj.symm, and_true, and_false, if_true, if_false]
        omega
      · rcases eq_or_ne t j with rfl | ht'
        · simp only [ht, Ne.symm ht, and_true, and_false, if_true, if_false]
          omega
        · simp [ht, ht', Ne.symm ht, Ne.symm ht']
    · simp [hb, Ne.symm hb]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hmaps : ∀ m ∈ g.support, (fun m : Fin r × Fin n →₀ ℕ => m (a0, l)) m ∈ Finset.range (ω (a0, l) + 1) := by
    intro m hm
    have := key m hm
    show m (a0, l) ∈ _
    rw [Finset.mem_range]
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun m => monomial m (coeff m g))
  exact (hfib.trans (as_sum g).symm).symm
end Formalism.GradedWeylDivisibility
