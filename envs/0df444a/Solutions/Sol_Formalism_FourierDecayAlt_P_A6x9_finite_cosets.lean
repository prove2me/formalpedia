-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.finite_cosets
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:34.339554+00:00
-- url     : https://prove2.me/submissions/3cb09fb9-21bb-4227-8f37-28f330b029e2

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)
namespace Formalism.FourierDecayAlt.P.A6x9
theorem _root_.solution {B : AddSubgroup K} (hB : IsOpen (B : Set K)) {Om : Set K}
    (hOm : IsCompact Om) : {w : K ⧸ B | (Quotient.out w : K) ∈ Om}.Finite := by
  have : DiscreteTopology (K ⧸ B) := QuotientAddGroup.discreteTopology hB
  obtain ⟨T, hT⟩ := hOm.elim_finite_subcover (fun w : K ⧸ B => {z : K | (z : K ⧸ B) = w})
    (fun w => (isOpen_discrete ({w} : Set (K ⧸ B))).preimage continuous_quot_mk)
    (fun z _ => Set.mem_iUnion.2 ⟨(z : K ⧸ B), rfl⟩)
  refine T.finite_toSet.subset ?_
  intro w hw
  obtain ⟨w', hw', h⟩ := Set.mem_iUnion₂.1 (hT hw)
  have h : ((Quotient.out w : K) : K ⧸ B) = w' := h
  rw [QuotientAddGroup.out_eq'] at h
  rw [h]
  exact hw'
end Formalism.FourierDecayAlt.P.A6x9
