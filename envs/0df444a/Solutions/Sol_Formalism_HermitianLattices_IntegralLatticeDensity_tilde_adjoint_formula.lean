-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.tilde_adjoint_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:35.23508+00:00
-- url     : https://prove2.me/submissions/94c9670b-84f9-4b07-a002-b64b13ec71b0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : TildeAdjoint := by
  unfold TildeAdjoint
  intro O M Q _ _ _ _ _ β hl hr hs ι _ a x y
  have hL : ∀ (s : Finset ι) (f : ι → M) (b : M), β (∑ i ∈ s, f i) b = ∑ i ∈ s, β (f i) b :=
    fun s f b => map_sum (AddMonoidHom.mk' (fun u => β u b) (fun u v => hl u v b)) f s
  have hR : ∀ (s : Finset ι) (f : ι → M) (u : M), β u (∑ i ∈ s, f i) = ∑ i ∈ s, β u (f i) :=
    fun s f u => map_sum (AddMonoidHom.mk' (fun v => β u v) (fun v w => hr u v w)) f s
  simp only [hL, hR, hs]
  exact Finset.sum_comm
end Formalism.HermitianLattices.IntegralLatticeDensity
