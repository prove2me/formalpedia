-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unramRelative
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:41.378869+00:00
-- url     : https://prove2.me/submissions/dea279ca-1404-4dc6-845d-f9361c1f0a5c

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x1
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.UnramRelative := by
  intro E _ _ _ hU
  have h := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 (maximalRealSubfield E)) (𝓞 E)
  unfold Unram at hU
  have h0 : (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≠ ⊥ := by
    rw [← hU]; exact differentIdeal_ne_bot
  have h1 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
    rw [hU] at h
    have h2 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) *
        (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) =
        1 * (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by rw [one_mul]; exact h.symm
    simpa using mul_right_cancel₀ h0 h2
  refine ⟨h1, fun g => ?_⟩
  unfold UnramAbove
  rw [h1, Ideal.isCoprime_iff_sup_eq]; simp
end Formalism.FourierDecayAlt.P
