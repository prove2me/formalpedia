-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmLift_xi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:20.989695+00:00
-- url     : https://prove2.me/submissions/05579fdd-d049-4d79-ab3e-e9879126cd75

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_mul
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_pow
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_minor0
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_minor1
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_cast
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_prod
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_antitone
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_rowsA
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_rowsB
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_D_eq
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_hw
import Theorems.Thm_Formalism_GradedWeylDivisibility_hw_weight_eq
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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) (hIL : bmIL lam sg) :
    bmLift R n lam (fun s => lam s - sg s) (hw R le_rfl sg) (xiB R lam sg) := by
  have hanti : Antitone lam := bmG_antitone lam fun i => (hIL i).2.trans (hIL i).1
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      bmLift R n ((sg i - nuNext lam i) • initW n (i.val + 1) + (lam i - sg i) • initW n (i.val + 1))
        ((sg i - nuNext lam i) • (0 : Fin n → ℕ) + (lam i - sg i) • Pi.single i 1)
        (bmG_D R n (i.val + 1) ^ (sg i - nuNext lam i) * bmG_D R n i.val ^ (lam i - sg i))
        (initMinor R (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
          initMinor R (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i)) := by
    intro i _
    have hs1 : i.val + 1 ≤ n := by omega
    have hs0 : i.val ≤ n := by omega
    refine bmLift_mul (bmLift_pow ?_ _) (bmLift_pow ?_ _)
    · rw [bmG_D_eq R n _ hs1, bmG_rowsA]
      exact bmLift_minor0 R n (Fin.castLE hs1) hs1
    · rw [bmG_D_eq R n _ hs0, bmG_rowsB]
      exact bmLift_minor1 R n (Fin.castLE hs0) hs1
  refine bmG_cast (bmG_prod Finset.univ _ _ _ _ hi) ?_ ?_ (bmG_hw R lam sg hIL) rfl
  · refine Eq.trans ?_ (hw_weight_eq lam hanti)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul]
    congr 1
    have h1 := hIL i
    omega
  · funext t
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero, zero_add,
      Pi.single_apply, mul_ite, mul_one]
    rw [Finset.sum_ite_eq]
    simp
end Formalism.BranchingDeterminantCap
