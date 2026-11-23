-- Prove2me | solution 1 for Formalism.CountingSumsFrames.comm_preserves_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:29.688942+00:00
-- url     : https://prove2.me/submissions/05c121fd-a1d2-47f6-bd7f-5fa55061cc67

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_cartan
import Theorems.Thm_Formalism_CountingSumsFrames_eig_supp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (T : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hT : ∀ x, T (glAct p LL j 0 0 x) = glAct p LL j 0 0 (T x)) :
    ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      T x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
  intro x hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmon : glAct p LL j 0 0 (monomial m (coeff m x)) = ((wt LL j 0 m : ℤ) : ℚ_[p]) • monomial m (coeff m x) := by
    ext m'
    rw [coeff_cartan, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  have h1 : glAct p LL j 0 0 (T (monomial m (coeff m x))) = ((wt LL j 0 m : ℤ) : ℚ_[p]) • T (monomial m (coeff m x)) := by
    rw [← hT, hmon, map_smul]
  have h2 := eig_supp LL j 0 _ _ h1
  rw [mem_restrictSupport_iff] at h2 ⊢
  intro m' hm'
  have h3 : wt LL j 0 m' = wt LL j 0 m := h2 hm'
  rw [mem_restrictSupport_iff] at hx
  have h4 := hx (Finset.mem_coe.mpr hm)
  simp only [Set.mem_ofPred_eq] at h4 ⊢
  rw [h3]; exact h4
end Formalism.CountingSumsFrames
