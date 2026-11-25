-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:38:54.624865+00:00
-- url     : https://prove2.me/submissions/87f1c374-b78c-4cb6-8234-66a2f2bff6df

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_isWH_of_comm
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_weight_rowW
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_rowcomp_comm_bmEL
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_claimT
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_list_eigen
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_IL_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_list_prod
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_isLow_iff
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_xi
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_xi_row
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_mem_alt
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_Zc
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_Zz
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_ZW
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_liftW
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_lead_eigen
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
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    bmZop R n lam sg (xiB R lam sg) = ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg := by
  have hIL := bm_IL_of lam sg hI
  have hxi := bmLift_xi (R := R) lam sg hIL
  have hZA : bmZop R n lam sg (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) =
      ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) •
        (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) := by
    rw [bmZop, bm_list_eigen (bmCap R n) (bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ))) _
      (bmK_lead_eigen lam sg hIL), bm_list_prod lam sg hI]
  refine sub_eq_zero.1 (bm_claimT lam sg _ ?_ ?_ ?_)
  · exact Submodule.sub_mem _ (bmK_mem_alt.1 (bmK_ZW lam sg _ _ (bmK_liftW hxi))).1 (Submodule.smul_mem _ _ hxi.1)
  · have hr := bm_xi_row (R := R) lam sg hIL
    have hr2 : IsWeightedHomogeneous (rowW (n + 1) n) (bmZop R n lam sg (xiB R lam sg)) (bmRho lam sg) :=
      bm_isWH_of_comm _ _ _ (bmK_Zc R n lam sg _ (bm_rowcomp_comm_bmEL R n _)) _ hr
    have hr3 : IsWeightedHomogeneous (rowW (n + 1) n)
        (bmZop R n lam sg (xiB R lam sg) - ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg)
        (bmRho lam sg) :=
      (weightedHomogeneousSubmodule R (rowW (n + 1) n) (bmRho lam sg)).sub_mem hr2
        ((weightedHomogeneousSubmodule R (rowW (n + 1) n) (bmRho lam sg)).smul_mem _ hr)
    intro m hm a
    have h4 := hr3 (mem_support_iff.1 hm)
    rw [← bm_weight_rowW, h4]
    simp [bmRho]
  · have e : bmZop R n lam sg (xiB R lam sg) - ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg =
        bmZop R n lam sg (xiB R lam sg - zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) -
          ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) •
            (xiB R lam sg - zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) := by
      rw [map_sub, hZA, smul_sub]; abel
    have eD : (omg fun s => (lam s : ℤ) - (sg s : ℤ)) = omg fun s => ((lam s - sg s : ℕ) : ℤ) := by
      congr 1
      funext s
      rw [Nat.cast_sub (hIL s).1]
    rw [e, eD, bm_isLow_iff]
    intro β hβ
    have h5 := (bm_isLow_iff _ _).1 hxi.2.2 β hβ
    rw [map_sub, map_smul, bmK_Zz, h5, map_zero, smul_zero, sub_zero]
end Formalism.BranchingDeterminantCap
