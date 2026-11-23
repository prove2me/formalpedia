-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.roots_finite_domain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:21.881386+00:00
-- url     : https://prove2.me/submissions/fa8a519d-53f7-4fcb-8ce8-6e51694b8f2c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
namespace Formalism.FourierDecayAlt.P.A6x5
theorem _root_.solution {F : Type} [CommRing F] [IsDomain F] (s : ℕ) (hs : 1 ≤ s) (d : F) :
    {x : F | x ^ s = d}.Finite := by
  classical
  refine (Polynomial.nthRoots s d).toFinset.finite_toSet.subset ?_
  intro x hx
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (Polynomial.mem_nthRoots hs).2 hx
end Formalism.FourierDecayAlt.P.A6x5
