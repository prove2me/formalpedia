-- Prove2me | solution 1 for Formalism.REAL.eabGlV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:20.723858+00:00
-- url     : https://prove2.me/submissions/ff5da020-94ea-4478-a8f9-5644937ff1e8

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_vector_complexified_derivative_sub
import Theorems.Thm_Formalism_REAL_vector_complexified_derivative_zero
import Theorems.Thm_Formalism_REAL_vector_complexified_derivative_commutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution (hl : RdLinV) (hb : RdBracketV) (hs : RdSmoothV) : EabGlV := by
  intro n ε E _ _ f a b c d g hf hg
  unfold EabV
  rw [vector_complexified_derivative_commutator hl hb hs ε f _ _ g hf hg, vector_complexified_derivative_sub hl hf hg]
  have h1 : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne]
      exact h
  have h2 : Matrix.single c d (1 : ℂ) * Matrix.single a b 1 =
      if d = a then Matrix.single c b 1 else 0 := by
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne]
      exact h
  rw [h1, h2]
  split_ifs <;> simp [vector_complexified_derivative_zero]
end Formalism.REAL
