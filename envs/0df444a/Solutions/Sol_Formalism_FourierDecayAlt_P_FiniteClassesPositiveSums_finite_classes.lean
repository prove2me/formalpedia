-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.finite_classes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:07.276261+00:00
-- url     : https://prove2.me/submissions/4b461c1b-9220-4e28-93a8-4187b81bd752

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
theorem _root_.solution [TopologicalSpace K] [IsTopologicalRing K] (hR : IsOpen (R : Set K))
    (Lc : Set K) (hLc : IsCompact Lc) :
    {y : K ⧸ R.toAddSubgroup | (Quotient.out y : K) ∈ Lc}.Finite := by
  have : DiscreteTopology (K ⧸ R.toAddSubgroup) := QuotientAddGroup.discreteTopology hR
  have h := (hLc.image (QuotientAddGroup.continuous_mk (N := R.toAddSubgroup))).finite_of_discrete
  refine h.subset ?_
  intro y hy
  exact ⟨Quotient.out y, hy, Quotient.out_eq' y⟩
end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
