-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_liftW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:51.566937+00:00
-- url     : https://prove2.me/submissions/24c3dd9f-979b-4022-9dae-a2ac4742ebea

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_mem_alt

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
    {G : BP R n} (h : bmLift R n lam b f G) : G ∈ bmW R n lam (∑ s, b s) := by
  exact bmK_mem_alt.mpr ⟨h.1, h.2.1⟩
end Formalism.BranchingDeterminantCap
