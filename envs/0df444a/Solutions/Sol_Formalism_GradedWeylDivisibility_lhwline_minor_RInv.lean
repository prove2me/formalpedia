-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_minor_RInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:15.783975+00:00
-- url     : https://prove2.me/submissions/64cb932d-4713-4d75-96c6-037960feacd3

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
theorem _root_.solution (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    lhwline_RInv (fun x : Fin r × Fin n → K => eval x (lpMinor K s hr hn)) := by
  intro x a b t hab
  simp only [lpMinor, RingHom.map_det]
  by_cases hb : b.val < s
  · have ha : a.val < s := lt_trans hab hb
    have hne : (⟨b.val, hb⟩ : Fin s) ≠ ⟨a.val, ha⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk] at this
      exact absurd this (ne_of_gt hab)
    refine Eq.trans ?_ (Matrix.det_updateRow_add_smul_self _ hne t)
    congr 1
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.updateRow_apply, lhwline_rowOp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hp : p = ⟨b.val, hb⟩
    · subst hp
      have e1 : Fin.castLE hr (⟨b.val, hb⟩ : Fin s) = b := Fin.ext (by simp)
      have e2 : Fin.castLE hr (⟨a.val, ha⟩ : Fin s) = a := Fin.ext (by simp)
      simp [e1, e2]
    · have hne2 : Fin.castLE hr p ≠ b := by
        intro h
        apply hp
        apply Fin.ext
        have h' := congrArg Fin.val h
        rw [Fin.coe_castLE] at h'
        simpa using h'
      simp [hp, hne2]
  · congr 1
    ext p q
    have hne2 : Fin.castLE hr p ≠ b := by
      intro h
      apply hb
      have h' := congrArg Fin.val h
      rw [Fin.coe_castLE] at h'
      have := p.isLt
      omega
    simp [lhwline_rowOp, hne2]
end Formalism.GradedWeylDivisibility
