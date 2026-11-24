-- Prove2me | solution 1 for Formalism.REAL.vector_right_derivative_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:18:50.837528+00:00
-- url     : https://prove2.me/submissions/a9b9c078-8a72-4adc-8a6a-b8de558e5b23

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_vector_right_derivative_neg
import Theorems.Thm_Formalism_REAL_vector_right_derivative_add

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
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.REAL
theorem _root_.solution (hl : RdLinV) {f : Matrix (Fin n) (Fin n) ℂ → E}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnGV ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : RdV (A - B) f g = RdV A f g - RdV B f g := by
  have hnB : inG ε (-B) := by
    unfold inG at hB ⊢
    rw [Matrix.conjTranspose_neg, neg_mul, mul_neg, ← neg_add, hB, neg_zero]
  rw [sub_eq_add_neg A B, vector_right_derivative_add hl hf hA hnB hg, vector_right_derivative_neg hl hf hB hg, ← sub_eq_add_neg]
end Formalism.REAL
