-- Prove2me | solution 1 for Formalism.SL.P.fu_comp_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:42.18925+00:00
-- url     : https://prove2.me/submissions/eb69029f-8054-4ab7-8ffe-be19bb9bade9

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementFU
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_NeighbourhoodHilbertSchmidtHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.SL Formalism.SL.P
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.SL.FU
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.SL.P
theorem _root_.solution {ι M N Q : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid Q]
    [Module ℂ M] [Module ℂ N] [Module ℂ Q] (s : Finset ι) (g : N →ₗ[ℂ] Q) (f : ι → M →ₗ[ℂ] N) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  ext x
  simp [LinearMap.sum_apply, map_sum]
end Formalism.SL.P
