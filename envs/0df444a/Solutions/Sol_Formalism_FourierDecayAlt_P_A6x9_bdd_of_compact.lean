-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.bdd_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:33.537677+00:00
-- url     : https://prove2.me/submissions/73840151-c542-406c-81aa-6f0b9bbb9154

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_pow_mem_mono

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
theorem _root_.solution (hd : LocalDatum K R ψ) (hπ : (π : K) ∈ R)
    (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {C : Set K} (hC : IsCompact C) :
    ∃ k : ℕ, ∀ z ∈ C, (π : K) ^ k * z ∈ R := by
  obtain ⟨k, hk⟩ := hC.elim_directed_cover (fun k : ℕ => {z | (π : K) ^ k * z ∈ R})
    (fun k => hd.isOpen.preimage (by fun_prop)) (fun z _ => Set.mem_iUnion.2 (hπ' z))
    (directed_of_isDirected_le (fun i j hij z hz => pow_mem_mono π hπ hij hz))
  exact ⟨k, hk⟩
end Formalism.FourierDecayAlt.P.A6x9
