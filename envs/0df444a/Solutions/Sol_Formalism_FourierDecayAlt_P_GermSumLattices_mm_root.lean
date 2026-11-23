-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.mm_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:50.673437+00:00
-- url     : https://prove2.me/submissions/6a2025ee-4733-44a0-81d3-8f8cf5234a10

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (h : MM R) (z : Kˣ) (n : ℕ) (hz : modK R (z : K) ^ (n + 1) = 1) :
    modK R (z : K) = 1 :=
  (pow_eq_one_iff_of_nonneg (h z z).1.le (Nat.succ_ne_zero n)).1 hz
end Formalism.FourierDecayAlt.P.GermSumLattices
