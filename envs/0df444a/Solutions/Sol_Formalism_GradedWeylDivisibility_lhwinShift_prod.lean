-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwinShift_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:53.347073+00:00
-- url     : https://prove2.me/submissions/f13df643-1809-47d6-b26d-da3269c4b5f9

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_one

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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, LhwinShift (P i) (μ i) δ) : LhwinShift (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (lhwinShift_one (R := R) (r := r) (n := n) δ)
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact lhwinShift_mul (h i (Finset.mem_insert_self _ _))
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))
end Formalism.GradedWeylDivisibility
