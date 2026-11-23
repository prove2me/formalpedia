-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.finrank_orthogonal_unit_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:43.462554+00:00
-- url     : https://prove2.me/submissions/abca0428-1fe7-41f5-a768-5f34d2406855

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg

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
theorem _root_.solution [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K) (v : V) (hv : h v v = 1) :
    finrank K (LinearMap.ker (h v)) + 1 = finrank K V := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (h v)
  have hr : LinearMap.range (h v) = ⊤ :=
    LinearMap.range_eq_top.2 (fun c => ⟨c • v, by simp [hv]⟩)
  rw [hr, finrank_top, finrank_self] at h1
  omega
end Formalism.FourierDecayAlt.P.S3x6
