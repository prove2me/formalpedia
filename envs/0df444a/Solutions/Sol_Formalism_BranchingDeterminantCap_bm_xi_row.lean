-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_xi_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:21.753838+00:00
-- url     : https://prove2.me/submissions/2ae318cf-0826-48bf-9d16-5e6d772d9d8d

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_antitone
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_initMinor_rowHom
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_sumA
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_sumB
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
    IsWeightedHomogeneous (rowW (n + 1) n) (xiB R lam sg) (bmRho lam sg) := by
  have hanti : Antitone lam := bmG_antitone lam fun i => (hIL i).2.trans (hIL i).1
  have h1 : IsWeightedHomogeneous (rowW (n + 1) n) (xiB R lam sg)
      (∑ i : Fin n, ((sg i - nuNext lam i) • initW (n + 1) (i.val + 1) +
        (lam i - sg i) • (initW (n + 1) i.val + Pi.single (Fin.last n) 1))) := by
    unfold xiB
    refine IsWeightedHomogeneous.prod _ _ _ fun i _ => ?_
    refine IsWeightedHomogeneous.mul (IsWeightedHomogeneous.pow ?_ _) (IsWeightedHomogeneous.pow ?_ _)
    · rw [← bmG_sumA]; exact bmG_initMinor_rowHom R _ _
    · rw [← bmG_sumB]; exact bmG_initMinor_rowHom R _ _
  convert h1 using 1
  funext a
  simp only [bmRho, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, initW, Pi.single_apply]
  by_cases ha : a.val < n
  · rw [dif_pos ha]
    have hne : a ≠ Fin.last n := fun h => by rw [h] at ha; simp at ha
    have h2 := congrFun (hw_weight_eq lam hanti) ⟨a.val, ha⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, initW] at h2
    have h3 : (∑ i : Fin n, ((sg i - nuNext lam i) * (if a.val < i.val + 1 then 1 else 0) +
        (lam i - sg i) * ((if a.val < i.val then 1 else 0) + if a = Fin.last n then 1 else 0))) +
        (lam ⟨a.val, ha⟩ - sg ⟨a.val, ha⟩) = lam ⟨a.val, ha⟩ := by
      have h4 : lam ⟨a.val, ha⟩ - sg ⟨a.val, ha⟩ =
          ∑ i : Fin n, if i = ⟨a.val, ha⟩ then (lam i - sg i) else 0 := by
        rw [Finset.sum_ite_eq']; simp
      rw [h4, ← Finset.sum_add_distrib]
      refine Eq.trans ?_ h2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [if_neg hne]
      have h5 := hIL i
      by_cases h6 : i.val = a.val
      · have h7 : i = ⟨a.val, ha⟩ := Fin.ext h6
        rw [if_pos h7, if_pos (by omega), if_neg (by omega)]
        omega
      · have h7 : i ≠ ⟨a.val, ha⟩ := fun h => h6 (by rw [h])
        rw [if_neg h7]
        by_cases h8 : a.val < i.val
        · rw [if_pos (by omega), if_pos h8]
          omega
        · rw [if_neg (by omega), if_neg h8]
          omega
    have h9 := (hIL ⟨a.val, ha⟩).1
    omega
  · rw [dif_neg ha]
    have hl : a = Fin.last n := Fin.ext (by have := a.isLt; simp; omega)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos hl, if_neg (by have := i.isLt; omega), if_neg (by have := i.isLt; omega)]
    omega
end Formalism.BranchingDeterminantCap
