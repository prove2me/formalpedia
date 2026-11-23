-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_comm_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:30.648656+00:00
-- url     : https://prove2.me/submissions/43606672-4473-4453-a715-b4887c81503b

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
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
    (k l q a j : Fin n) :
    E k l * bmF E u q a j - bmF E u q a j * E k l =
      (if l = a then bmF E u q k j else 0) - (if k = j then bmF E u q a l else 0) := by
  have h := hE k l a j
  unfold bmF
  set c : Module.End R M := ((u + ((q : ℕ) : ℤ) : ℤ) : Module.End R M) with hc
  have hcc : c * E k l = E k l * c := bmA_cast_comm _ _
  have h1 : E k l * ((if a = j then c else 0) - E a j) - ((if a = j then c else 0) - E a j) * E k l =
      - (E k l * E a j - E a j * E k l) := by
    by_cases haj : a = j
    · simp only [haj, if_true]
      have : E k l * (c - E j j) - (c - E j j) * E k l =
          - (E k l * E j j - E j j * E k l) - (c * E k l - E k l * c) := by noncomm_ring
      rw [this, hcc]; noncomm_ring
    · simp only [haj, if_false]; noncomm_ring
  rw [h1, h]
  by_cases hla : l = a <;> by_cases hkj : k = j
  · subst hla; subst hkj; simp
  · subst hla; simp [hkj]
  · subst hkj; simp [hla, Ne.symm hla]
  · simp [hla, hkj]
end Formalism.BranchingDeterminantCap
