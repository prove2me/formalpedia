-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehwShift_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:23.237188+00:00
-- url     : https://prove2.me/submissions/8212f543-99a3-4a30-b92a-1820ca10b903

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_one
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
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ} {ι : Type*}
    (s : Finset ι) (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, LehwShift w (P i) (μ i) δ) : LehwShift w (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using lehwShift_one (R := R) w δ
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact lehwShift_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end Formalism.GradedWeylDivisibility
