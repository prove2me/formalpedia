-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmLift_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:50.196301+00:00
-- url     : https://prove2.me/submissions/abf4c5a6-f036-4f03-8e2d-9f9ab451c71e

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_lastW_castSucc
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_zmon
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_emb
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_WH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_low
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowStable


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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) R}
    {G : BP R n} (g : Matrix (Fin n) (Fin n) R) (h : bmLift R n lam b f G) :
    bmLift R n lam b (rowAct R g f) (rowAct R (extM R g) G) := by
  refine ⟨dualWeylRowStable R (n + 1) n lam (extM R g) G h.1, ?_, ?_⟩
  · exact bmF_rowAct_WH R (lastW n) (fun a b s => by rw [bmF_lastW_castSucc, bmF_lastW_castSucc]) g G _ h.2.1
  · have h1 := bmF_rowAct_low R g _ _ h.2.2
    rwa [map_sub, map_mul, bmF_rowAct_zmon, bmF_rowAct_emb] at h1
end Formalism.BranchingDeterminantCap
