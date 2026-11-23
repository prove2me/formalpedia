-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.finite_cosets
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:12.014297+00:00
-- url     : https://prove2.me/submissions/c142d9ab-afca-47dc-81ae-900095c42c9a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
namespace Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
theorem _root_.solution {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (Λ : AddSubgroup K) (hΛ : IsOpen (Λ : Set K)) (C : Set K) (hC : IsCompact C) :
    {y : K ⧸ Λ | (Quotient.out y : K) ∈ C}.Finite := by
  have : DiscreteTopology (K ⧸ Λ) := QuotientAddGroup.discreteTopology hΛ
  have h1 : (((↑) : K → K ⧸ Λ) '' C).Finite :=
    (hC.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine h1.subset ?_
  intro y hy
  exact ⟨Quotient.out y, hy, QuotientAddGroup.out_eq' y⟩
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
