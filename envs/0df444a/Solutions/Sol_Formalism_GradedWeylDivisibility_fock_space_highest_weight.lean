-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fock_space_highest_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:13.749079+00:00
-- url     : https://prove2.me/submissions/efaee287-1f74-4a2e-b6c0-047e89de892f

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_eval_idFrame_hw
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowGraded
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwLine
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_kill
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_diag
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
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : FockQHW := by
  intro r n hn ν hν F hF
  classical
  set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F with hGdef
  have hG : G ∈ dualWeyl ℚ r n ν := dualWeylRowGraded ℚ r n ν _ F hF
  have hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν) :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨c, hc⟩ := hwLine ℚ r n hn ν hν G hG
    (fun a b hab k hk => lehw_kill hn ν hν G hG hGh a b hab k hk)
  have hHW := hwRowWeight ℚ r n hn ν hν
  have h1 : fockQ (hw ℚ hn ν) F = fockQ (hw ℚ hn ν) G := by
    unfold fockQ
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hm))]
  have h2 : fockQ (hw ℚ hn ν) G = c * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
    rw [hc]
    unfold fockQ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_smul, smul_eq_mul]
    ring
  have hcolF : IsWeightedHomogeneous (colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1
  have hcolH : IsWeightedHomogeneous (colW r n) (hw ℚ hn ν) ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp (hwMem ℚ r n hn ν hν)).1
  have hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idFrame ℚ r n (a, j) = 0 := by
    intro a j h
    simp [idFrame, h]
  have eF := lhwline_diag hn ν F hcolF (idFrame ℚ r n) hD
  have eH := lhwline_diag hn ν (hw ℚ hn ν) hcolH (idFrame ℚ r n) hD
  have hev1 := lehw_eval_idFrame_hw hn ν
  have hDmem : lhwline_mnu hn ν ∈ (hw ℚ hn ν).support := by
    rw [mem_support_iff]
    intro h0
    rw [h0, zero_mul, hev1] at eH
    exact one_ne_zero eH
  have hcoef : coeff (lhwline_mnu hn ν) F = c * coeff (lhwline_mnu hn ν) (hw ℚ hn ν) := by
    have e : coeff (lhwline_mnu hn ν) F = coeff (lhwline_mnu hn ν) G := by
      rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hDmem))]
    rw [e, hc, coeff_smul, smul_eq_mul]
  have hevF : eval (idFrame ℚ r n) F = c := by
    rw [eF, hcoef, mul_assoc, ← eH, hev1, mul_one]
  rw [h1, h2, hevF]
end Formalism.GradedWeylDivisibility
