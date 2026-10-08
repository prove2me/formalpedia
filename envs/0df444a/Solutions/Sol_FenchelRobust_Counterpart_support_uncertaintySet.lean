-- Prove2me | solution 1 for FenchelRobust.Counterpart.support_uncertaintySet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:36:07.645293+00:00
-- url     : https://prove2.me/submissions/de966aad-4c5b-45da-b131-b15da619e7bc

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_Model

open FenchelRobust.Counterpart in
theorem solution {m L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (v : Fin m → ℝ) :
    supportFun (uncertaintySet a0 A Z) v =
      ((a0 ⬝ᵥ v : ℝ) : EReal) + supportFun Z (Matrix.mulVec A.transpose v) := by
  set c : ℝ := a0 ⬝ᵥ v with hc
  have key : ∀ z : Fin L → ℝ, v ⬝ᵥ (a0 + A.mulVec z) = c + (A.transpose.mulVec v) ⬝ᵥ z := by
    intro z
    rw [dotProduct_add, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm v a0]
  have hL : supportFun (uncertaintySet a0 A Z) v
      = ⨆ z ∈ Z, (((c + (A.transpose.mulVec v) ⬝ᵥ z : ℝ)) : EReal) := by
    unfold supportFun uncertaintySet
    apply le_antisymm
    · refine iSup₂_le ?_
      rintro a ⟨z, hz, rfl⟩
      rw [key z]
      exact le_iSup₂ (f := fun z (_ : z ∈ Z) => (((c + (A.transpose.mulVec v) ⬝ᵥ z : ℝ)) : EReal)) z hz
    · refine iSup₂_le ?_
      intro z hz
      rw [← key z]
      exact le_iSup₂ (f := fun a (_ : a ∈ {a | ∃ ζ ∈ Z, a = a0 + A.mulVec ζ}) =>
        ((v ⬝ᵥ a : ℝ) : EReal)) (a0 + A.mulVec z) ⟨z, hz, rfl⟩
  rw [hL]
  unfold supportFun
  set w := A.transpose.mulVec v
  apply le_antisymm
  · refine iSup₂_le ?_
    intro z hz
    rw [EReal.coe_add]
    gcongr
    exact le_iSup₂ (f := fun z (_ : z ∈ Z) => ((w ⬝ᵥ z : ℝ) : EReal)) z hz
  · set M := ⨆ z ∈ Z, (((c + w ⬝ᵥ z : ℝ)) : EReal)
    have h1 : (⨆ z ∈ Z, ((w ⬝ᵥ z : ℝ) : EReal)) ≤ ((-c : ℝ) : EReal) + M := by
      refine iSup₂_le ?_
      intro z hz
      have h := le_iSup₂ (f := fun z (_ : z ∈ Z) => (((c + w ⬝ᵥ z : ℝ)) : EReal)) z hz
      have h2 : ((-c : ℝ) : EReal) + (((c + w ⬝ᵥ z : ℝ)) : EReal) ≤ ((-c : ℝ) : EReal) + M := by
        gcongr
      rw [← EReal.coe_add] at h2
      simpa using h2
    calc ((c : ℝ) : EReal) + (⨆ z ∈ Z, ((w ⬝ᵥ z : ℝ) : EReal))
        ≤ ((c : ℝ) : EReal) + (((-c : ℝ) : EReal) + M) := by gcongr
      _ = M := by
        rw [← add_assoc, ← EReal.coe_add]
        simp
