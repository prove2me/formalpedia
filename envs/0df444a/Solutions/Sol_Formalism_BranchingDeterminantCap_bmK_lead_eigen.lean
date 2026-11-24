-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_lead_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:17.226229+00:00
-- url     : https://prove2.me/submissions/d8e1f37b-1b53-4775-88ed-7e0c54febc26

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndE_self
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_lead
import Theorems.Thm_Formalism_BranchingDeterminantCap_capDet_eigen
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_mem_dualWeyl_iff
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_antitone
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hIL : bmIL lam sg) (u : ℤ) :
    bmCap R n u (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) =
      ((bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ)) u : ℤ) : R) •
        (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) := by
  have hwm : hw R le_rfl sg ∈ dualWeyl R n n sg := hwMem R n n le_rfl sg (bmK_antitone lam sg hIL)
  have hwm' := bm_mem_dualWeyl_iff.1 hwm
  have h1 := capDet_eigen (bmEL R n) u (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg))
    (fun s => (sg s : ℤ))
    (fun l j hlj => by
      show bmE R n l j _ = 0
      rw [bmE_lead, hwm'.2 l j hlj, map_zero, mul_zero])
    (fun s => by
      show bmE R n s s _ = _
      rw [bmE_lead, bm_ndE_self, hwm'.1 s, map_smul, mul_smul_comm]
      simp)
  have h2 : bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ)) u = ∏ j : Fin n, (u + ((j : ℕ) : ℤ) - (sg j : ℤ)) := by
    unfold bmChi
    refine Finset.prod_congr rfl fun j _ => ?_
    beta_reduce
    rw [Nat.cast_sub (hIL j).1]
    ring
  rw [h2]
  exact h1
end Formalism.BranchingDeterminantCap
