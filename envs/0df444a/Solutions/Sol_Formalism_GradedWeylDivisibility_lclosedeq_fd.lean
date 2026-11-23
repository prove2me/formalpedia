-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lclosedeq_fd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:59.638828+00:00
-- url     : https://prove2.me/submissions/bb8d6dfc-7341-45e9-b9a5-726592a0c358

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
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
theorem _root_.solution (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := by
  classical
  have hS : Set.Finite {d : Fin r × Fin n →₀ ℕ | Finsupp.weight (colW r n) d = ν} := by
    refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : Fin r × Fin n => ν v.2))).subset ?_
    intro d hd
    have hd' : Finsupp.weight (colW r n) d = ν := hd
    show d ≤ _
    rw [Finsupp.le_def]
    intro v
    have h1 : d v ≤ Finsupp.weight (colW r n) d v.2 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      by_cases hv : v ∈ d.support
      · refine le_trans ?_ (Finset.single_le_sum
          (f := fun u => (d u • colW r n u) v.2) (fun _ _ => Nat.zero_le _) hv)
        simp [colW]
      · have : d v = 0 := by
          by_contra h
          exact hv (Finsupp.mem_support_iff.mpr h)
        rw [this]
        exact Nat.zero_le _
    rw [hd'] at h1
    simpa using h1
  haveI := hS.to_subtype
  haveI hfd : FiniteDimensional ℚ (weightedHomogeneousSubmodule ℚ (colW r n) ν) := by
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
    exact Module.Finite.equiv (AddMonoidAlgebra.supportedEquivFinsupp
      {d : Fin r × Fin n →₀ ℕ | Finsupp.weight (colW r n) d = ν}).symm
  exact Submodule.finiteDimensional_of_le (fun f hf => (Submodule.mem_inf.mp hf).1)
end Formalism.GradedWeylDivisibility
