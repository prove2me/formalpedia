-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NthRootMeasurability.image_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:14.169798+00:00
-- url     : https://prove2.me/submissions/2beccfe4-a7a7-441e-9aa5-14d9e7cb8900

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_R_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NthRootMeasurability
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.NthRootMeasurability
theorem _root_.solution (s k : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) :
    (fun z => u⁻¹ * z ^ s) '' A s k = {0}ᶜ := by
  ext c
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, A, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨hz, _⟩, rfl⟩
    exact mul_ne_zero (inv_ne_zero hu) (pow_ne_zero _ hz)
  · intro hc
    refine ⟨R s k (u * c), ⟨?_, ?_⟩, ?_⟩
    · intro h0
      have := R_pow s k hs (u * c)
      rw [h0, zero_pow hs] at this
      exact mul_ne_zero hu hc this.symm
    · rw [R_pow s k hs]
    · rw [R_pow s k hs, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
end Formalism.FourierDecayAlt.P.NthRootMeasurability
