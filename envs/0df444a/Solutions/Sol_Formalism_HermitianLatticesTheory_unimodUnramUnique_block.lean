-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:01.191314+00:00
-- url     : https://prove2.me/submissions/3b3450a9-2d5c-4d04-933f-4d3bb20b9e79

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ]
    (IH : ∀ A : Matrix κ κ R, Aᴴ = A → IsUnit A.det →
      ∃ g : Matrix κ κ R, IsUnit g.det ∧ gᴴ * A * g = 1)
    (B : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R) (hB : Bᴴ = B) (hdet : IsUnit B.det)
    (h1 : B (Sum.inl ()) (Sum.inl ()) = 1) :
    ∃ g : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R, IsUnit g.det ∧ gᴴ * B * g = 1 := by
  have hB11 : B.toBlocks₁₁ = 1 := by
    ext a b; cases a; cases b; simpa [toBlocks₁₁] using h1
  set P := B.toBlocks₁₂
  set Q := B.toBlocks₂₁
  set D₀ := B.toBlocks₂₂
  have hBe : B = fromBlocks 1 P Q D₀ := by rw [← hB11, fromBlocks_toBlocks]
  rw [hBe] at hB hdet ⊢
  rw [fromBlocks_conjTranspose] at hB
  obtain ⟨-, hQP, hPQ, hD₀⟩ := fromBlocks_inj.1 hB
  rw [det_fromBlocks_one₁₁] at hdet
  have hD : (D₀ - Q * P)ᴴ = D₀ - Q * P := by
    rw [conjTranspose_sub, conjTranspose_mul, hD₀, hPQ, hQP]
  obtain ⟨g', hg', hg'D⟩ := IH _ hD hdet
  refine ⟨fromBlocks 1 (-(P * g')) 0 g', ?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_one, one_mul]; exact hg'
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]
    rw [← hg'D]
    simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg, conjTranspose_mul, hPQ]
    congr 1 <;> simp [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] <;> abel
end Formalism.HermitianLatticesTheory
