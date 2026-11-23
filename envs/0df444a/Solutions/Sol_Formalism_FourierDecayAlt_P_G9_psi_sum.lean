-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.psi_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:10.577531+00:00
-- url     : https://prove2.me/submissions/b69be412-bfb5-4b43-9ff3-b4a2bfddc9b4

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution (β : ℂ) {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    psi β (∑ k ∈ s, f k) = ∏ k ∈ s, psi β (f k) := by
  unfold psi
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum, Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum]
end Formalism.FourierDecayAlt.P.G9
