-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_minor_CInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:17.360486+00:00
-- url     : https://prove2.me/submissions/2cb31616-43ac-4734-950c-be7493416fcf

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
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
variable {K : Type} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution [Infinite K] (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    lhwline_CInv (fun x : Fin r × Fin n → K => eval x (lpMinor K s hr hn)) := by
  intro x l j c hlj
  simp only [lpMinor, RingHom.map_det]
  by_cases hj : j.val < s
  · have hl : l.val < s := lt_trans hlj hj
    have hne : (⟨j.val, hj⟩ : Fin s) ≠ ⟨l.val, hl⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk] at this
      exact absurd this (ne_of_gt hlj)
    refine Eq.trans ?_ (Matrix.det_updateCol_add_smul_self _ hne c)
    congr 1
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.updateCol_apply, lhwline_colOp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hq : q = ⟨j.val, hj⟩
    · subst hq
      have e1 : Fin.castLE hn (⟨j.val, hj⟩ : Fin s) = j := Fin.ext (by simp)
      have e2 : Fin.castLE hn (⟨l.val, hl⟩ : Fin s) = l := Fin.ext (by simp)
      simp [e1, e2]
    · have hne2 : Fin.castLE hn q ≠ j := by
        intro h
        apply hq
        apply Fin.ext
        have h' := congrArg Fin.val h
        rw [Fin.coe_castLE] at h'
        simpa using h'
      simp [hq, hne2]
  · congr 1
    ext p q
    have hne2 : Fin.castLE hn q ≠ j := by
      intro h
      apply hj
      have h' := congrArg Fin.val h
      rw [Fin.coe_castLE] at h'
      have := q.isLt
      omega
    simp [lhwline_colOp, hne2]
end Formalism.GradedWeylDivisibility
