-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmD_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:02.851247+00:00
-- url     : https://prove2.me/submissions/98782fdf-c257-407d-a10b-9593c01da52e

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndEul_eq
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmZ_euler
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_mem_dualWeyl_iff
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_isWH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_bmE
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_bmZ

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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ)
    (G : BP R n) (hG : G ∈ dualWeyl R (n + 1) n lam) (β : Fin n → ℤ) (s : Fin n) :
    bmE R n s s (zcomp R n β G) = (((lam s : ℤ) - β s : ℤ) : R) • zcomp R n β G := by
  have hG' := (bm_mem_dualWeyl_iff.mp hG).1 s
  rw [bm_ndEul_eq, Derivation.add_apply] at hG'
  have h1 := congrArg (zcomp R n β) hG'
  rw [map_add, bmD_zcomp_bmE, map_smul] at h1
  have h2 : zcomp R n β (bmZ R n s s G) = ((β s : ℤ) : R) • zcomp R n β G := by
    rw [bmD_zcomp_bmZ, sub_self, sub_zero]
    exact bmZ_euler R n β s _ (bmD_zcomp_isWH β G)
  rw [h2] at h1
  rw [eq_sub_of_add_eq h1]
  push_cast
  rw [sub_smul]
end Formalism.BranchingDeterminantCap
