-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dualWeyl_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:20:20.152137+00:00
-- url     : https://prove2.me/submissions/7972e233-686e-4f55-8d8a-a1963b653bff

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_one_mem_dualWeyl

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
    (ν : ι → Fin n → ℕ) (f : ι → MvPolynomial (Fin r × Fin n) R)
    (hf : ∀ i ∈ s, f i ∈ dualWeyl R r n (ν i)) :
    (∏ i ∈ s, f i) ∈ dualWeyl R r n (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one_mem_dualWeyl (R := R) (r := r) (n := n))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact dualWeyl_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
end Formalism.GradedWeylDivisibility
