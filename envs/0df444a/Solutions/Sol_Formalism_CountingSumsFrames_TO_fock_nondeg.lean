-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.fock_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:03.282801+00:00
-- url     : https://prove2.me/submissions/0e5be54c-c42d-40e4-940a-910de052ee42

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_fock_monomial
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {σ : Type} (z : MvPolynomial σ ℚ_[p]) (h : ∀ y, fock p z y = 0) : z = 0 := by
  by_contra hz
  obtain ⟨m, hm⟩ : ∃ m, m ∈ z.support := by
    by_contra hc; push Not at hc
    exact hz (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  have h1 := Formalism.CountingSumsFrames.fock_monomial z m hm
  rw [h] at h1
  have h2 : (m.prod fun _ k => (k.factorial : ℚ_[p])) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => by exact_mod_cast Nat.factorial_ne_zero _
  exact (mul_ne_zero (mem_support_iff.mp hm) h2) h1.symm
end Formalism.CountingSumsFrames.TO
