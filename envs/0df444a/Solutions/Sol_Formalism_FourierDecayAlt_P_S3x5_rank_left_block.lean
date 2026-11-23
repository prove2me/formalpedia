-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.rank_left_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:00.362993+00:00
-- url     : https://prove2.me/submissions/830951e0-27d5-425c-8663-8103547450d1

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {ν α β : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (J : Matrix ν ν K) (X : Matrix ν α K) (Y : Matrix ν β K)
    (S : Matrix (α ⊕ β) (α ⊕ β) K) (hS : IsUnit S.det)
    (h : (fromCols X Y)ᴴ * J * fromCols X Y = S) : X.rank = Fintype.card α := by
  have hL : (S⁻¹ * ((fromCols X Y)ᴴ * J)) * fromCols X Y = 1 := by
    rw [Matrix.mul_assoc, h, nonsing_inv_mul _ hS]
  have hX : X = fromCols X Y * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K) := by
    rw [fromCols_mul_fromRows]; simp
  have hM : ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
      (S⁻¹ * ((fromCols X Y)ᴴ * J))) * X = 1 := by
    calc _ = ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
          (S⁻¹ * ((fromCols X Y)ᴴ * J))) *
          (fromCols X Y * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K)) := by
          rw [← hX]
      _ = (fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
          (((S⁻¹ * ((fromCols X Y)ᴴ * J)) * fromCols X Y) *
            (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K)) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hL, Matrix.one_mul, fromCols_mul_fromRows]
          simp
  apply le_antisymm (rank_le_card_width X)
  have := rank_mul_le_right ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
      (S⁻¹ * ((fromCols X Y)ᴴ * J))) X
  rw [hM, rank_one] at this
  exact this
end Formalism.FourierDecayAlt.P.S3x5
