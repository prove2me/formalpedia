-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.densityProduct_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:34.950354+00:00
-- url     : https://prove2.me/submissions/e4ca34aa-1458-4a81-8503-8badb7d6a9a7

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
open Finset Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (η : ℤ) (q : ℕ) (lo mid hi : ℤ) (h1 : lo ≤ mid + 1) (h2 : mid ≤ hi) :
    densP η q lo hi = densP η q lo mid * densP η q (mid + 1) hi := by
  unfold densP
  rw [← Finset.prod_union]
  · congr 1
    ext i
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  · rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_Icc] at hi1 hi2
    omega
end Formalism.FourierDecayAlt.P.S3x5
