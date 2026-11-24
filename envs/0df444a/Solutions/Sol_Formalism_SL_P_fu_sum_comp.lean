-- Prove2me | solution 1 for Formalism.SL.P.fu_sum_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:43.276543+00:00
-- url     : https://prove2.me/submissions/dc190b01-a6af-4479-a2ce-ddd5646053b0

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
    [Module ℂ M] [Module ℂ N] [Module ℂ Q] (s : Finset ι) (f : ι → N →ₗ[ℂ] Q) (g : M →ₗ[ℂ] N) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  ext x
  simp [LinearMap.sum_apply]
end Formalism.SL.P
