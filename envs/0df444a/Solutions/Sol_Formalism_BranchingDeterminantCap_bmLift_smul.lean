-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmLift_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:21.574244+00:00
-- url     : https://prove2.me/submissions/f96c93a7-4a64-4869-ac1a-1a3f9109a266

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_isWeightedHomogeneous_smul
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) R}
    {G : BP R n} (c : R) (h : bmLift R n lam b f G) : bmLift R n lam b (c • f) (c • G) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Submodule.smul_mem _ c h1, isWeightedHomogeneous_smul h2 c, ?_⟩
  have e : c • G - zmon R n b * emb R n (c • f) = c • (G - zmon R n b * emb R n f) := by
    rw [map_smul, smul_sub, mul_smul_comm]
  rw [e]
  exact bmF_low_smul c h3
end Formalism.BranchingDeterminantCap
