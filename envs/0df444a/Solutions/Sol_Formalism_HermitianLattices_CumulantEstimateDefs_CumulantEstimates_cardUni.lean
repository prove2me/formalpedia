-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.cardUni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:43.65035+00:00
-- url     : https://prove2.me/submissions/3e5fbc2c-0a4d-484f-b46b-887a8d2da55e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution (F : Type) [Field F] [Fintype F] (r : ℕ) (blk : Fin r → ℕ) :
    Nat.card {A : Matrix (Fin r) (Fin r) F // ∀ i j, blk j ≤ blk i → A i j = if i = j then 1 else 0} =
      Fintype.card F ^ (univ.filter (fun ij : Fin r × Fin r => blk ij.1 < blk ij.2)).card := by
  classical
  have e : {A : Matrix (Fin r) (Fin r) F // ∀ i j, blk j ≤ blk i → A i j = if i = j then 1 else 0} ≃
      ({ij : Fin r × Fin r // blk ij.1 < blk ij.2} → F) :=
    { toFun := fun A ij => A.1 ij.1.1 ij.1.2
      invFun := fun g => ⟨fun i j => if h : blk i < blk j then g ⟨(i, j), h⟩ else if i = j then 1 else 0,
        fun i j hij => by simp [not_lt.2 hij]⟩
      left_inv := fun A => by
        apply Subtype.ext
        funext i j
        by_cases h : blk i < blk j
        · simp [h]
        · simp [h, A.2 i j (not_lt.1 h)]
      right_inv := fun g => by
        funext ij
        simp [ij.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
