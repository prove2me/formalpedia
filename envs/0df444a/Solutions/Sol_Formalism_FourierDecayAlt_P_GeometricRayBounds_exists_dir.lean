-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GeometricRayBounds.exists_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:18:14.404838+00:00
-- url     : https://prove2.me/submissions/e6f79657-7020-44b2-8048-eefe4a9f4de4

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragingVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GeometricRayBounds
namespace Formalism.FourierDecayAlt.P.GeometricRayBounds
theorem _root_.solution {ι : Type*} (S : Finset ι) (c : ι → ℂ) (hc : ∀ i ∈ S, c i ≠ 0) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ i ∈ S, (c i * u).re ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ S.image (fun i => (c i).re / (c i).im) := by
    first
    | exact Infinite.exists_not_mem_finset _
    | exact Infinite.exists_notMem_finset _
  refine ⟨1 + (t : ℂ) * Complex.I, ?_, fun i hi => ?_⟩
  · intro h
    have h1 := congrArg Complex.re h
    simp at h1
  · intro h0
    have h0' : (c i).re = (c i).im * t := by
      simp at h0
      linarith
    by_cases him : (c i).im = 0
    · exact hc i hi (Complex.ext (by rw [h0', him, zero_mul, Complex.zero_re])
        (by rw [him, Complex.zero_im]))
    · exact ht (Finset.mem_image.2 ⟨i, hi, by rw [h0']; exact mul_div_cancel_left₀ t him⟩)
end Formalism.FourierDecayAlt.P.GeometricRayBounds
