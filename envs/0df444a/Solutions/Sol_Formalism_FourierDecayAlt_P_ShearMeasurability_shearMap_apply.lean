-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ShearMeasurability.shearMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:06.742801+00:00
-- url     : https://prove2.me/submissions/0e71c655-d151-4051-95d8-054e40c62084

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability
import Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_eSplit_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.ShearMeasurability
variable {m : ℕ} (w : Equiv.Perm (Fin m))
namespace Formalism.FourierDecayAlt.P.ShearMeasurability
theorem _root_.solution (x : C2.Lidx m → ℂ) (q : C2.Lidx m) :
    mulMap w (eSplit w x) q = x q + ∑ k, aX w x q.1.1 k * bX w x k q.1.2 := by
  classical
  have hA : ∀ i k, (∑ t : C2.LPidx w, if t.1 = (i, k) then x ⟨t.1, t.2.1⟩ else 0) = aX w x i k := by
    intro i k
    unfold aX
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨(i, k), h⟩]
      · simp
      · intro t _ ht
        rw [if_neg]
        intro e
        exact ht (Subtype.ext e)
      · simp
    · apply Finset.sum_eq_zero
      intro t _
      rw [if_neg]
      intro e
      apply h
      have h2 := t.2
      rw [e] at h2
      exact h2
  have hB : ∀ k j, (∑ t : C2.Lstidx w, if t.1 = (k, j) then x ⟨t.1, t.2.1⟩ else 0) = bX w x k j := by
    intro k j
    unfold bX
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨(k, j), h⟩]
      · simp
      · intro t _ ht
        rw [if_neg]
        intro e
        exact ht (Subtype.ext e)
      · simp
    · apply Finset.sum_eq_zero
      intro t _
      rw [if_neg]
      intro e
      apply h
      have h2 := t.2
      rw [e] at h2
      exact h2
  have hexp : ∀ i j, (C2.lowOf (fun t : C2.LPidx w => t.1) (fun t => x ⟨t.1, t.2.1⟩) *
      C2.lowOf (fun t : C2.Lstidx w => t.1) (fun t => x ⟨t.1, t.2.1⟩)) i j =
      (1 : Matrix (Fin m) (Fin m) ℂ) i j + bX w x i j + aX w x i j + ∑ k, aX w x i k * bX w x k j := by
    intro i j
    simp only [C2.lowOf]
    rw [add_mul, mul_add, mul_add]
    simp only [one_mul, mul_one, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, hA, hB]
    ring
  have hne : q.1.1 ≠ q.1.2 := (ne_of_lt q.2).symm
  have hab : aX w x q.1.1 q.1.2 + bX w x q.1.1 q.1.2 = x q := by
    unfold aX bX
    by_cases h : w.symm q.1.2 < w.symm q.1.1
    · rw [dif_pos ⟨q.2, h⟩, dif_neg (fun h' => lt_asymm h h'.2)]
      simp
    · have h' : w.symm q.1.1 < w.symm q.1.2 :=
        lt_of_le_of_ne (not_lt.1 h) (fun e => hne (w.symm.injective e))
      rw [dif_neg (fun h'' => h h''.2), dif_pos ⟨q.2, h'⟩]
      simp
  simp only [mulMap, eSplit_apply]
  rw [hexp, Matrix.one_apply_ne hne]
  linear_combination hab
end Formalism.FourierDecayAlt.P.ShearMeasurability
