-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.cut_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:30.093236+00:00
-- url     : https://prove2.me/submissions/93b7aeed-c3ff-44fd-874b-4181efc930c3

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (R : Subring K) (hRo : IsOpen (R : Set K)) {S : Set K} (hS : IsCompact S)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (hcr : IsCr R cr) : {x | (cr x : K) ∈ S}.Finite := by
  have : DiscreteTopology (K ⧸ R.toAddSubgroup) := QuotientAddGroup.discreteTopology hRo
  have h1 : IsCompact ((QuotientAddGroup.mk : K → K ⧸ R.toAddSubgroup) '' S) :=
    hS.image QuotientAddGroup.continuous_mk
  refine h1.finite_of_discrete.subset ?_
  intro x hx
  exact ⟨cr x, hx, hcr x⟩
end Formalism.FourierDecayAlt.P.GermSumLattices
