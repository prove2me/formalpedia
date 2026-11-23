-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmLift_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:17.880735+00:00
-- url     : https://prove2.me/submissions/3b86f304-6c56-421d-b5e7-440b3f901fe5

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_omg_add
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_add
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_fil_of_WH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_fil_add_low
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_fil_mul_low
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_lead_WH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_zmon_add
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_mul
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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {lam b lam' b' : Fin n → ℕ}
    {f f' : MvPolynomial (Fin n × Fin n) R} {G G' : BP R n} (h : bmLift R n lam b f G)
    (h' : bmLift R n lam' b' f' G') : bmLift R n (lam + lam') (b + b') (f * f') (G * G') := by
  refine ⟨dualWeyl_mul h.1 h'.1, ?_, ?_⟩
  · have := h.2.1.mul h'.2.1
    rwa [← Finset.sum_add_distrib] at this
  · have e1 : G * G' - zmon R n (b + b') * emb R n (f * f') =
        (zmon R n b * emb R n f) * (G' - zmon R n b' * emb R n f') +
          G' * (G - zmon R n b * emb R n f) := by
      rw [bmF_zmon_add, map_mul]; ring
    have e2 : omg (fun s => (((b + b') s : ℕ) : ℤ)) = omg (fun s => (b s : ℤ)) + omg (fun s => (b' s : ℤ)) := by
      have e3 : (fun s => (((b + b') s : ℕ) : ℤ)) = (fun s => (b s : ℤ)) + fun s => (b' s : ℤ) := by
        funext s
        simp
      rw [e3, bmF_omg_add]
    rw [e1, e2]
    refine bmF_low_add (bmF_fil_mul_low (bmF_fil_of_WH (bmF_lead_WH R n b f)) h'.2.2) ?_
    rw [add_comm (omg _)]
    refine bmF_fil_mul_low ?_ h.2.2
    have : G' = zmon R n b' * emb R n f' + (G' - zmon R n b' * emb R n f') := by ring
    rw [this]
    exact bmF_fil_add_low (bmF_fil_of_WH (bmF_lead_WH R n b' f')) h'.2.2
end Formalism.BranchingDeterminantCap
