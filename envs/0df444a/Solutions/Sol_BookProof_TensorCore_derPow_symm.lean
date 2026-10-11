-- Prove2me | solution 1 for BookProof.TensorCore.derPow_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:09.824496+00:00
-- url     : https://prove2.me/submissions/8d31fda1-7736-4462-b49a-df22a178623c

-- Generated from ChapterTensorGraphCore.lean — solution of BookProof.TensorCore.derPow_symm
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TensorCore_derPow_symm_tmul
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFarisLavineCore
open BookProof.TensorCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hA : SymmetricOn D₂ A) (n : ℕ) :
    ∀ x y : ((domSpace Hs D₂).pow n),
      (inner ℂ (derPow Hs D₂ A n x) (inclPow Hs D₂ n y) : ℂ)
        = inner ℂ (inclPow Hs D₂ n x) (derPow Hs D₂ A n y) := by

  induction n with
  | zero => intro x y; simp [derPow]
  | succ n ih =>
      have hlinL : ∀ (x y : (Hs.pow (n + 1)).carrier) (r : ℂ),
          inner ℂ (r • x) y = star r * inner ℂ x y := fun x y r => inner_smul_left x y r
      -- first: `x` an elementary tensor, `y` arbitrary
      have hpure : ∀ (a : D₂) (b : ((domSpace Hs D₂).pow n))
          (y : ((domSpace Hs D₂).pow (n + 1))),
          (inner ℂ (derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)) (inclPow Hs D₂ (n + 1) y) : ℂ)
            = inner ℂ (inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b)) (derPow Hs D₂ A (n + 1) y) := by
        intro a b y
        have hy : y ∈ Submodule.span ℂ
            {t : (D₂ ⊗[ℂ] ((domSpace Hs D₂).pow n).carrier) |
              ∃ (p : D₂) (q : ((domSpace Hs D₂).pow n)), p ⊗ₜ[ℂ] q = t} := by
          rw [TensorProduct.span_tmul_eq_top]; trivial
        have hlin : ∀ (x y : (Hs.pow (n + 1)).carrier) (r : ℂ),
            inner ℂ x (r • y) = r * inner ℂ x y := fun x y r => inner_smul_right x y r
        induction hy using Submodule.span_induction with
        | mem t ht =>
            obtain ⟨c, d, rfl⟩ := ht
            exact derPow_symm_tmul Hs D₂ A hA n ih a c b d
        | zero => simp
        | add s t _ _ hs ht => simp only [map_add, inner_add_right, hs, ht]
        | smul r s _ hs => rw [map_smul, map_smul, hlin, hlin, hs]
      -- then: `x` arbitrary
      intro x y
      have hx : x ∈ Submodule.span ℂ
          {t : (D₂ ⊗[ℂ] ((domSpace Hs D₂).pow n).carrier) |
            ∃ (p : D₂) (q : ((domSpace Hs D₂).pow n)), p ⊗ₜ[ℂ] q = t} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨a, b, rfl⟩ := ht
          exact hpure a b y
      | zero => simp
      | add s t _ _ hs ht => simp only [map_add, inner_add_left, hs, ht]
      | smul r s _ hs => rw [map_smul, map_smul, hlinL, hlinL, hs]
