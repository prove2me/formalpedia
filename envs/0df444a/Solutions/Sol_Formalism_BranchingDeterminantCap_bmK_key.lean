-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:15:00.193849+00:00
-- url     : https://prove2.me/submissions/deb932d2-e5d9-466c-a41c-df98460cf138

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_isLow_iff
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_add
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_smul
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_kill
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_liftW
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
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (f : MvPolynomial (Fin n × Fin n) R) (G G' : BP R n)
    (h : bmLift R n lam (fun s => lam s - sg s) f G) (h' : bmLift R n lam (fun s => lam s - sg s) f G') :
    bmZop R n lam sg G = bmZop R n lam sg G' := by
  have h0 : bmLift R n lam (fun s => lam s - sg s) 0 (G - G') := by
    have := bmLift_add h (bmLift_smul (-1 : R) h')
    simpa [sub_eq_add_neg] using this
  have hz : zcomp R n (fun s => ((lam s - sg s : ℕ) : ℤ)) (G - G') = 0 := by
    have hlow := h0.2.2
    rw [map_zero, mul_zero, sub_zero] at hlow
    exact (bm_isLow_iff _ _).mp hlow _ le_rfl
  have hk := bmK_kill lam sg hI (G - G') (bmK_liftW h0) hz
  rw [map_sub] at hk
  exact sub_eq_zero.mp hk
end Formalism.BranchingDeterminantCap
