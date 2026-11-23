-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:38.119808+00:00
-- url     : https://prove2.me/submissions/63a2dab7-1b13-45a9-8256-9c49efb0dbdf

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
variable {K : Type*} [Field K]
namespace Formalism.FourierDecayAlt.P.S3x4
theorem _root_.solution {A B U : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (R : A →ₗ[K] B) (f : A →ₗ[K] U)
    (h : LinearMap.ker R ≤ LinearMap.ker f) : ∃ S : B →ₗ[K] U, ∀ x, S (R x) = f x := by
  obtain ⟨σ, hσ⟩ := R.rangeRestrict.exists_rightInverse_of_surjective R.range_rangeRestrict
  obtain ⟨τ, hτ⟩ := LinearMap.exists_extend σ
  refine ⟨f ∘ₗ τ, fun x => ?_⟩
  have h1 : τ (R x) = σ ⟨R x, LinearMap.mem_range_self R x⟩ := by
    rw [← hτ]; rfl
  have h2 : R (σ ⟨R x, LinearMap.mem_range_self R x⟩) = R x := by
    have := congrArg (fun φ => ((φ ⟨R x, LinearMap.mem_range_self R x⟩ : LinearMap.range R) : B)) hσ
    simpa using this
  have h3 : σ ⟨R x, LinearMap.mem_range_self R x⟩ - x ∈ LinearMap.ker f := by
    apply h; simp [h2]
  rw [LinearMap.comp_apply, h1]
  have := LinearMap.mem_ker.mp h3
  rw [map_sub, sub_eq_zero] at this
  exact this
end Formalism.FourierDecayAlt.P.S3x4
