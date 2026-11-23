-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_list_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:32.340546+00:00
-- url     : https://prove2.me/submissions/277ef4dd-c63c-42fa-ba97-d55b97271a6b

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_IL_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmH_flatMap_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    ((bmList lam sg).map (bmChi lam fun s => ((lam s - sg s : ℕ) : ℤ))).prod =
      cCap (lamZ lam) (fun i => (sg i : ℤ)) := by
  have hIL := bm_IL_of lam sg hI
  have hcast : ∀ s, ((lam s - sg s : ℕ) : ℤ) = (lam s : ℤ) - (sg s : ℤ) := fun s =>
    Nat.cast_sub (hIL s).1
  unfold bmList cCap capEig
  rw [bmH_flatMap_prod, Finset.prod_map_toList]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [List.map_map, Finset.prod_map_toList]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Function.comp, bmChi]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hcast]
  ring
end Formalism.BranchingDeterminantCap
