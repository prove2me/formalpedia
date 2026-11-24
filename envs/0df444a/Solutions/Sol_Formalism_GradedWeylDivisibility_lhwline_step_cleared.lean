-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_step_cleared
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:18.1975+00:00
-- url     : https://prove2.me/submissions/9a4f38f0-85ee-45a4-9540-ef9ea7653196

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_step_apply
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
theorem _root_.solution (k : ℕ) (hr : k < r) (hn : k < n) (y : Fin r × Fin n → K)
    (hy : lhwline_cleared k y) (hp : y (⟨k, hr⟩, ⟨k, hn⟩) ≠ 0) :
    lhwline_cleared (k + 1) (highestWeightLineUpdate ⟨k, hr⟩ ⟨k, hn⟩ y) := by
  intro a j haj hak
  rw [lhwline_step_apply]
  have hkk := hp
  simp only [Fin.lt_def, Fin.val_mk] at haj hak ⊢
  rcases lt_trichotomy a.val k with ha | ha | ha
  · have h1 : y (a, j) = 0 := hy a j haj (Or.inl ha)
    have h2 : y (a, ⟨k, hn⟩) = 0 := hy a ⟨k, hn⟩ (by simp only [Fin.val_mk]; omega) (Or.inl ha)
    simp [show ¬ k < a.val by omega, h1, h2]
  · have ha' : a = ⟨k, hr⟩ := Fin.ext ha
    subst ha'
    simp only [Fin.val_mk] at haj hak ⊢
    rcases lt_or_gt_of_ne (Ne.symm haj) with hj | hj
    · have h1 : y (⟨k, hr⟩, j) = 0 := hy _ j (by simp only [Fin.val_mk]; omega) (Or.inr hj)
      simp [h1, show ¬ k < j.val by omega]
    · simp only [lt_self_iff_false, if_false, if_pos hj]
      field_simp
      ring
  · have hj : j.val ≤ k := by omega
    simp only [if_pos ha, if_neg (show ¬ k < j.val by omega), add_zero]
    rcases lt_or_eq_of_le hj with hj | hj
    · have h1 : y (a, j) = 0 := hy a j haj (Or.inr hj)
      have h2 : y (⟨k, hr⟩, j) = 0 := hy _ j (by simp only [Fin.val_mk]; omega) (Or.inr hj)
      simp [h1, h2]
    · have hj' : j = ⟨k, hn⟩ := Fin.ext hj
      subst hj'
      field_simp
      ring
end Formalism.GradedWeylDivisibility
