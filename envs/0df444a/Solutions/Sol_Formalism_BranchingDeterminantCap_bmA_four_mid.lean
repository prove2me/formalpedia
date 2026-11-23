-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_four_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:46.261053+00:00
-- url     : https://prove2.me/submissions/97101f5b-aec7-4201-b581-31b4c2326597

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_two
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_cast_comm
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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (p p' : Fin n) (hp : p'.val = p.val + 1) (a b i j : Fin n) :
    bmF E u p a i * bmF E u p' b j - bmF E u p b j * bmF E u p' a i =
      bmF E u p b i * bmF E u p' a j - bmF E u p a j * bmF E u p' b i := by
  have hc : ((u + ((p' : ℕ) : ℤ) : ℤ) : Module.End R M) = ((u + ((p : ℕ) : ℤ) : ℤ) : Module.End R M) + 1 := by
    rw [hp]; push_cast; abel
  unfold bmF
  rw [hc, bmA_two _ _ _ (bmA_cast_comm _ _) (bmA_cast_comm _ _), bmA_two _ _ _ (bmA_cast_comm _ _) (bmA_cast_comm _ _),
    hE a i b j, hE b i a j]
  simp only [eq_comm (a := i) (b := b), eq_comm (a := i) (b := a)]
  abel
end Formalism.BranchingDeterminantCap
