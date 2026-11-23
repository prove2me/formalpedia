-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.roots_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:09.94285+00:00
-- url     : https://prove2.me/submissions/6920d1e4-59f9-41d6-a901-f1b8b5d4efd8

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_roots_finite_domain

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
theorem _root_.solution {K : Type} [CommRing K] [IsArtinianRing K] [IsReduced K] (s : ℕ)
    (hs : 1 ≤ s) (d : K) : {x : K | x ^ s = d}.Finite := by
  have h1 : (Set.pi Set.univ fun I : MaximalSpectrum K =>
      {x : K ⧸ I.asIdeal | x ^ s = IsArtinianRing.equivPi K d I}).Finite :=
    Set.Finite.pi fun I => roots_finite_domain s hs _
  refine (h1.preimage ((IsArtinianRing.equivPi K).injective.injOn)).subset ?_
  intro x hx I _
  have hx' : x ^ s = d := hx
  change IsArtinianRing.equivPi K x I ^ s = IsArtinianRing.equivPi K d I
  rw [← hx', map_pow, Pi.pow_apply]
end Formalism.FourierDecayAlt.P.A6x5
