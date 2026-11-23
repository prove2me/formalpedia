-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.adic_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:52.873044+00:00
-- url     : https://prove2.me/submissions/f05da6c9-6218-48c8-8654-8493e617906e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_mul


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
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}
variable [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (h : Adic R ϖ) {C : Set K} (hC : IsCompact C) : ∃ a : ℕ, ∀ x ∈ C, Bd R ϖ a x := by
  obtain ⟨a, ha⟩ := hC.elim_directed_cover (fun a : ℕ => {x : K | (ϖ : K) ^ a * x ∈ R})
    (fun a => h.isOpen.preimage (continuous_const.mul continuous_id))
    (fun x _ => by
      obtain ⟨m, hm⟩ := h.absorb x
      exact Set.mem_iUnion.2 ⟨m, hm⟩)
    (Monotone.directed_le (by
      intro a b hab x hx
      exact Bd.mono h.mem hab hx))
  exact ⟨a, fun x hx => ha hx⟩
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
