-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.CoeffHom.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:08.221975+00:00
-- url     : https://prove2.me/submissions/e15d6d6d-2177-40a1-8ff0-bb2a8f3cfc23

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_one
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
namespace CoeffHom
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → Fin n → ℕ)
    (h : ∀ i ∈ s, CoeffHom (P i) (μ i)) : CoeffHom (∏ i ∈ s, P i) (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CoeffHom.one (R := R) (r := r) (n := n))
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))
end CoeffHom
end Formalism.GradedWeylDivisibility
