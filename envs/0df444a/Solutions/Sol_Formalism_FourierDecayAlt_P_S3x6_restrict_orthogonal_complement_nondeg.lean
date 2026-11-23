-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.restrict_orthogonal_complement_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:41.111361+00:00
-- url     : https://prove2.me/submissions/dfc9889a-fbdc-4fbc-ba05-a7995d62ddc9

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_restrict_form_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h) (hn : Nondeg h) (v : V)
    (hv : h v v = 1) : Nondeg (restrictFormAlt h (LinearMap.ker (h v))) := by
  intro w hw
  apply Subtype.ext
  apply hn
  intro z
  have hz : z - h v z • v ∈ LinearMap.ker (h v) := by
    simp [LinearMap.mem_ker, hv]
  have h1 := hw ⟨_, hz⟩
  have h2 : h w v = 0 := by
    rw [← hh v w]
    have := w.2
    rw [LinearMap.mem_ker] at this
    rw [this, map_zero]
  rw [restrict_form_apply] at h1
  simpa [map_sub, h2] using h1
end Formalism.FourierDecayAlt.P.S3x6
