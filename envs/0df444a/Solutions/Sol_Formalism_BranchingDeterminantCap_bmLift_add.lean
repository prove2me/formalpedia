-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmLift_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:11.861442+00:00
-- url     : https://prove2.me/submissions/8d409a9d-34a1-4871-8144-be46f324060a

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_add

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f f' : MvPolynomial (Fin n × Fin n) R}
    {G G' : BP R n} (h : bmLift R n lam b f G) (h' : bmLift R n lam b f' G') :
    bmLift R n lam b (f + f') (G + G') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨Submodule.add_mem _ h1 h1', h2.add h2', ?_⟩
  have e : G + G' - zmon R n b * emb R n (f + f') =
      (G - zmon R n b * emb R n f) + (G' - zmon R n b * emb R n f') := by
    rw [map_add]
    ring
  rw [e]
  exact bmF_low_add h3 h3'
end Formalism.BranchingDeterminantCap
