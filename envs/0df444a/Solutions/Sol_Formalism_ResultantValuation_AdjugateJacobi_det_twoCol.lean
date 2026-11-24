-- Prove2me | solution 1 for Formalism.ResultantValuation.AdjugateJacobi.det_twoCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:40.234837+00:00
-- url     : https://prove2.me/submissions/2c82f2fb-656c-460b-9a5e-a6bc977dabde

import Definitions.Def_Formalism_ResultantValuation_KoszulSecondDifferential
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.AdjugateJacobi
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.ResultantValuation.AdjugateJacobi
theorem _root_.solution {k i : n} (hki : k ≠ i) (u v : n → R) :
    (twoCol k i u v).det = u k * v i - u i * v k := by
  classical
  let p : n → Prop := fun a => a ≠ k ∧ a ≠ i
  have h : ∀ a, ¬p a → ∀ b, p b → twoCol k i u v a b = 0 := by
    intro a ha b hb
    have hab : a ≠ b := by
      rintro rfl
      exact ha hb
    simp only [twoCol, updateCol_ne hb.2, updateCol_ne hb.1, one_apply_ne hab]
  rw [twoBlockTriangular_det _ p h]
  have h1 : (toSquareBlockProp (twoCol k i u v) p).det = 1 := by
    have : toSquareBlockProp (twoCol k i u v) p = 1 := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      rw [toSquareBlockProp_def, of_apply]
      simp only [twoCol, updateCol_ne hb.2, updateCol_ne hb.1]
      by_cases hab : a = b
      · subst hab; simp
      · rw [one_apply_ne hab, one_apply_ne (fun h => hab (congrArg Subtype.val h))]
    rw [this, det_one]
  rw [h1, one_mul]
  let f : Fin 2 → { a // ¬p a } := ![⟨k, fun h => h.1 rfl⟩, ⟨i, fun h => h.2 rfl⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [f, Subtype.ext_iff, Ne.symm hki]
    · rintro ⟨a, ha⟩
      simp only [p, not_and_or, not_not] at ha
      rcases ha with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  let e : Fin 2 ≃ { a // ¬p a } := Equiv.ofBijective f hf
  rw [← det_submatrix_equiv_self e, det_fin_two]
  simp [e, f, toSquareBlockProp_def, twoCol, updateCol_apply, hki]
  ring
end Formalism.ResultantValuation.AdjugateJacobi
