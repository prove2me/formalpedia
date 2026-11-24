-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmD_raise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:02.641461+00:00
-- url     : https://prove2.me/submissions/50716b78-a725-4044-845c-a96bf333fef4

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndE_eq
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_mem_dualWeyl_iff
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_omg_sub
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_omg_single
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_bmE
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_bmZ
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zero_of_gt

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
    (G : BP R n) (hG : G ∈ dualWeyl R (n + 1) n lam) (β : Fin n → ℤ)
    (hmax : ∀ β', zcomp R n β' G ≠ 0 → omg β' ≤ omg β) (l j : Fin n) (hlj : l < j) :
    bmE R n l j (zcomp R n β G) = 0 := by
  have hG' := (bm_mem_dualWeyl_iff.mp hG).2 l j hlj
  rw [bm_ndE_eq, Derivation.add_apply] at hG'
  have h1 := congrArg (zcomp R n β) hG'
  rw [map_add, bmD_zcomp_bmE, bmD_zcomp_bmZ, map_zero] at h1
  have h0 : zcomp R n (β - (Pi.single l 1 - Pi.single j 1)) G = 0 := by
    apply bmD_zero_of_gt G β hmax
    rw [bmD_omg_sub, bmD_omg_sub, bmD_omg_single, bmD_omg_single]
    have : (l : ℕ) < (j : ℕ) := hlj
    omega
  rw [h0, map_zero, add_zero] at h1
  exact h1
end Formalism.BranchingDeterminantCap
