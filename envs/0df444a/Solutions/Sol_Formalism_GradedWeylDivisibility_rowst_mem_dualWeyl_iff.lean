-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowst_mem_dualWeyl_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:04.88661+00:00
-- url     : https://prove2.me/submissions/e0888c72-429f-4678-93a6-bc02811d6f29

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas

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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule, AlgHom.toLinearMap_apply]
end Formalism.GradedWeylDivisibility
