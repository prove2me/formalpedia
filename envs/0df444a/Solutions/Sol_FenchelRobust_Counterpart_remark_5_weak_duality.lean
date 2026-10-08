-- Prove2me | solution 1 for FenchelRobust.Counterpart.remark_5_weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:13:42.049035+00:00
-- url     : https://prove2.me/submissions/82b5b9cc-66c5-4e81-9c05-7cf5a880add1

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_Model

open FenchelRobust.Counterpart in
theorem solution {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (v : Fin m → ℝ) :
    worstCase a0 A Z D f x ≤ frcValue a0 A Z D f x v ∧
      (frcValue a0 A Z D f x v ≤ 0 → RobustFeasible a0 A Z D f x) := by
  have key : ∀ a ∈ uncertaintySet a0 A Z ∩ D x,
      ((f a x : ℝ) : EReal) ≤ frcValue a0 A Z D f x v := by
    rintro a ⟨⟨ζ, hζ, rfl⟩, haD⟩
    have hs : ((Matrix.mulVec A.transpose v ⬝ᵥ ζ : ℝ) : EReal)
        ≤ supportFun Z (Matrix.mulVec A.transpose v) := by
      unfold supportFun
      exact le_iSup₂ (f := fun ζ (_ : ζ ∈ Z) =>
        ((Matrix.mulVec A.transpose v ⬝ᵥ ζ : ℝ) : EReal)) ζ hζ
    have hc : concaveConj (D x) (fun a => f a x) v
        ≤ (((a0 + A.mulVec ζ) ⬝ᵥ v - f (a0 + A.mulVec ζ) x : ℝ) : EReal) := by
      unfold concaveConj
      exact iInf₂_le (f := fun a (_ : a ∈ D x) =>
        ((a ⬝ᵥ v - f a x : ℝ) : EReal)) _ haD
    have h1 : ((a0 ⬝ᵥ v : ℝ) : EReal) + ((Matrix.mulVec A.transpose v ⬝ᵥ ζ : ℝ) : EReal)
        ≤ ((a0 ⬝ᵥ v : ℝ) : EReal) + supportFun Z (Matrix.mulVec A.transpose v) :=
      add_le_add le_rfl hs
    have h2 := EReal.sub_le_sub h1 hc
    unfold frcValue
    refine le_trans (le_of_eq ?_) h2
    rw [← EReal.coe_add, ← EReal.coe_sub]
    congr 1
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, add_dotProduct,
      dotProduct_comm (A.mulVec ζ) v]
    ring
  have hw : worstCase a0 A Z D f x ≤ frcValue a0 A Z D f x v := by
    unfold worstCase
    exact iSup₂_le key
  refine ⟨hw, fun h0 a ha haD => ?_⟩
  have := le_trans (key a ⟨ha, haD⟩) h0
  exact_mod_cast this
