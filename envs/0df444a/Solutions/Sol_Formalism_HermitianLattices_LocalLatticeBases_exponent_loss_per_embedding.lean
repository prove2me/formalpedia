-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.exponent_loss_per_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:02.41349+00:00
-- url     : https://prove2.me/submissions/eab8dcb2-d35f-4e38-a3d2-755d4579329b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : ExponentLossPerEmbedding := by
  intro ι Ψ p _ W nu C N t hW ht htN hnu
  have : ∑ τ ∈ Ψ, (2 * W τ + C * N + if p τ then nu τ else 0) ≤ ∑ τ ∈ Ψ, (4 * W τ + (C+1) * N) := by
    apply Finset.sum_le_sum
    intro τ hτ
    split_ifs with h
    · linarith [hnu τ hτ h, hW τ hτ]
    · linarith [hW τ hτ]
  refine this.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring
end Formalism.HermitianLattices.LocalLatticeBases
