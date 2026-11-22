-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gb_norm_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:07.652335+00:00
-- url     : https://prove2.me/submissions/b69323f7-756d-4860-a5ac-68f5e4c45ed6

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset
open scoped ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {θ : V →ₗ[ℂ] V}
    (h : IsSelfAdjointInvolution θ) (x : V) : ‖θ x‖ = ‖x‖ := by
  have e : ‖θ x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h.2, h.1]
  have h1 := norm_nonneg (θ x)
  have h2 := norm_nonneg x
  nlinarith [e]
end Formalism.HermitianLatticeCounting.P
