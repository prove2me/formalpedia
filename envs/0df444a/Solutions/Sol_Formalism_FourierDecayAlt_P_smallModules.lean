-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.smallModules
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:13.357194+00:00
-- url     : https://prove2.me/submissions/367c4003-0c73-49ea-8b40-2e353017f2a6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_pow_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_image_pow_eq_preimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.SmallModules := by
  intro K _ _ _ R ψ hD hn V hV
  obtain ⟨ϖ, hϖR, hϖ⟩ := hD.unif
  obtain ⟨N, hN⟩ := pow_small hD hn ϖ hϖR hϖ V hV
  have hset : ((Submodule.span R {(ϖ : K) ^ N} : Submodule R K) : Set K) =
      (fun r => (ϖ : K) ^ N * r) '' (R : Set K) := by
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_span_singleton, Set.mem_image]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(a : K), a.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  refine ⟨Submodule.span R {(ϖ : K) ^ N}, ⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.coe_toAddSubgroup, hset, image_pow_eq_preimage]
    exact hD.isOpen.preimage (continuous_const.mul continuous_id)
  · rw [Submodule.coe_toAddSubgroup, hset]
    exact hD.isCompact.image (continuous_const.mul continuous_id)
  · rw [hset]
    rintro _ ⟨r, hr, rfl⟩
    exact hN r hr
end Formalism.FourierDecayAlt.P
