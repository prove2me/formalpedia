-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_fin_cpt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:13.002774+00:00
-- url     : https://prove2.me/submissions/997a7a54-8105-4c72-ac44-65746421af29

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {Q : Type} (Λ : AddSubgroup K) (hΛ : IsOpen (Λ : Set K)) (s : Q → K)
    (hinj : ∀ q q', s q - s q' ∈ Λ → q = q') (hsurj : ∀ y : K, ∃ q, y - s q ∈ Λ) {C : Set K}
    (hC : IsCompact C) : {q | s q ∈ C}.Finite := by
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun q : Q => {y : K | y - s q ∈ Λ})
    (fun q => hΛ.preimage (continuous_id.sub continuous_const))
    (fun y _ => by
      obtain ⟨q, hq⟩ := hsurj y
      exact Set.mem_iUnion.2 ⟨q, hq⟩)
  refine t.finite_toSet.subset ?_
  intro q hq
  obtain ⟨q', hq', h⟩ := Set.mem_iUnion₂.1 (ht hq)
  rw [hinj q q' h]
  exact hq'
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
