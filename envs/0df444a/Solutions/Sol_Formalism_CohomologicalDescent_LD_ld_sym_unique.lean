-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_sym_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:04.332603+00:00
-- url     : https://prove2.me/submissions/29314008-16eb-49bf-88f9-7081f500c7b0

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_symmetric_block_weight_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_nu_ne
import Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_weight_colW_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_weight_rowW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (q w : ℕ) (μ : Fin (1 + q) → ℕ) (x : MvPolynomial (Fin (1 + q) × Fin (1 + q)) ℤ)
    (hx : x ∈ nablaWt (1 + q) (blockWt 1 q w fun _ => 0) μ) (hne : x ≠ 0) :
    ∑ a, μ a = w ∧ ∃ c : ℤ, x = c • ∏ a, X (a, ldZ q) ^ μ a := by
  have key : ∀ d ∈ x.support, d = ∑ a, Finsupp.single (a, ldZ q) (μ a) ∧ ∑ a, μ a = w := by
    intro d hd
    have hd' := MvPolynomial.mem_support_iff.mp hd
    have hcolw : Finsupp.weight (colW (1 + q) (1 + q)) d = blockWt 1 q w fun _ => 0 := hx.1.1 hd'
    have hroww : Finsupp.weight (rowW (1 + q) (1 + q)) d = μ := hx.2 hd'
    have hcol : ∀ s, ∑ a, d (a, s) = blockWt 1 q w (fun _ => 0) s := fun s => by
      rw [← lccomp_weight_colW_apply, hcolw]
    have hrow : ∀ a, rowDeg d a = μ a := fun a => by
      rw [← ldrow_weight_rowW, hroww]
    have hzero : ∀ a s, s ≠ ldZ q → d (a, s) = 0 := by
      intro a s hs
      have h1 := hcol s
      rw [ld_sym_nu_ne q w s hs] at h1
      exact (Finset.sum_eq_zero_iff.mp h1) a (Finset.mem_univ a)
    have hdz : ∀ a, d (a, ldZ q) = μ a := by
      intro a
      rw [← hrow a]
      unfold rowDeg
      exact (Finset.sum_eq_single (ldZ q) (fun s _ hs => hzero a s hs)
        (fun h => absurd (Finset.mem_univ _) h)).symm
    constructor
    · ext ⟨a, s⟩
      rw [Finsupp.finsetSum_apply]
      by_cases hs : s = ldZ q
      · subst hs
        rw [Finset.sum_eq_single a]
        · rw [Finsupp.single_eq_same, hdz]
        · intro b _ hb
          exact Finsupp.single_eq_of_ne (by intro h; exact hb (Prod.mk.inj h).1.symm)
        · intro h
          exact absurd (Finset.mem_univ _) h
      · rw [hzero a s hs]
        symm
        refine Finset.sum_eq_zero fun b _ => ?_
        exact Finsupp.single_eq_of_ne (by intro h; exact hs (Prod.mk.inj h).2)
    · have h1 := hcol (ldZ q)
      rw [symmetric_block_weight_zero] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun a _ => (hdz a).symm
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
  refine ⟨(key d hd).2, coeff (∑ a, Finsupp.single (a, ldZ q) (μ a)) x, ?_⟩
  have hprod : ∏ a, (X (a, ldZ q) : MvPolynomial (Fin (1 + q) × Fin (1 + q)) ℤ) ^ μ a =
      monomial (∑ a, Finsupp.single (a, ldZ q) (μ a)) 1 := by
    rw [monomial_sum_one]
    exact Finset.prod_congr rfl fun a _ => X_pow_eq_monomial
  rw [hprod]
  ext d'
  rw [coeff_smul, coeff_monomial]
  by_cases hd' : ∑ a, Finsupp.single (a, ldZ q) (μ a) = d'
  · rw [if_pos hd', hd', smul_eq_mul, mul_one]
  · rw [if_neg hd', smul_zero]
    by_contra hc
    exact hd' (key d' (MvPolynomial.mem_support_iff.mpr hc)).1.symm
end Formalism.CohomologicalDescent.LD
