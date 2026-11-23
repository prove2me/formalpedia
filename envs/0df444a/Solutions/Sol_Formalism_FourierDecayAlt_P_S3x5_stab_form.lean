-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.stab_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:00.590003+00:00
-- url     : https://prove2.me/submissions/50ce2eaa-4212-4f55-b00a-5bd2f84eacb4

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
theorem _root_.solution {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (T : Matrix α α K) (T' : Matrix β β K) (hdT : IsUnit T.det)
    (k : Matrix (α ⊕ β) (α ⊕ β) K) (h1 : k * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K) =
      (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K))
    (h2 : kᴴ * fromBlocks T 0 0 T' * k = fromBlocks T 0 0 T') :
    ∃ d : Matrix β β K, k = fromBlocks 1 0 0 d ∧ dᴴ * T' * d = T' := by
  obtain ⟨A, B, C, d, rfl⟩ : ∃ A B C d, k = fromBlocks A B C d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks k).symm⟩
  rw [fromBlocks_mul_fromRows] at h1
  obtain ⟨hA, hC⟩ := fromRows_inj h1
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero] at hA hC
  subst hA; subst hC
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h2
  obtain ⟨-, hB, -, hd⟩ := h2
  simp only [conjTranspose_one, Matrix.one_mul, conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at hB hd
  have hB0 : B = 0 := by
    have := congrArg (fun M => T⁻¹ * M) hB
    simpa [← Matrix.mul_assoc, nonsing_inv_mul T hdT] using this
  subst hB0
  refine ⟨d, rfl, ?_⟩
  simpa using hd
end Formalism.FourierDecayAlt.P.S3x5
