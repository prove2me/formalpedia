-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_mono_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:57.67072+00:00
-- url     : https://prove2.me/submissions/e6075ea1-246b-413c-9548-16ba0a30f95b

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_weight_col
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_mnu_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (hn : n ≤ r) (ν : Fin n → ℕ)
    (g : MvPolynomial (Fin r × Fin n) K) (hg : IsWeightedHomogeneous (colW r n) g ν)
    (D : Fin r × Fin n → K) (hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → D (a, j) = 0)
    (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ g.support) (hne : m ≠ lhwline_mnu hn ν) :
    ∏ v, D v ^ m v = 0 := by
  by_contra hprod
  apply hne
  have hoff : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → m (a, j) = 0 := by
    intro a j h
    by_contra hm0
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ (a, j)) (by rw [hD a j h, zero_pow hm0]))
  have hw : Finsupp.weight (colW r n) m = ν := hg (mem_support_iff.mp hm)
  ext ⟨a, j⟩
  rw [lhwline_mnu_apply]
  split_ifs with h
  · have hc := congrFun hw j
    rw [lhwline_weight_col, Finset.sum_eq_single a] at hc
    · exact hc
    · intro b _ hb
      exact hoff b j (by intro hbj; exact hb (Fin.ext (by omega)))
    · simp
  · exact hoff a j h
end Formalism.GradedWeylDivisibility
