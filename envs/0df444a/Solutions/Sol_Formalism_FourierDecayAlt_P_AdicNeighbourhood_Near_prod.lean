-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.Near.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:40.333486+00:00
-- url     : https://prove2.me/submissions/e1af1df6-7dbe-4dac-aa21-15c56e546716

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_near_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Near_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
namespace Near
theorem _root_.solution {ι : Type} {a : K} (ha : a ∈ R) (S : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ S, Near R a (f i)) : Near R a (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using near_one a
  | insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul ha (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
end Near
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
