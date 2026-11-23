-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.classes_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:54.701653+00:00
-- url     : https://prove2.me/submissions/5244a1ea-5798-4710-9359-05711c2f37e3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution (h : Ctx K R ϖ) {C : Set K} (hC : IsCompact C) :
    {x : K ⧸ R.toAddSubgroup | ∃ c ∈ C, ((c : K) : K ⧸ R.toAddSubgroup) = x}.Finite := by
  have hd : DiscreteTopology (K ⧸ R.toAddSubgroup) :=
    QuotientAddGroup.discreteTopology h.isOpen
  exact (hC.image QuotientAddGroup.continuous_mk).finite_of_discrete
end Formalism.FourierDecayAlt.P.HenselRootsBounded
