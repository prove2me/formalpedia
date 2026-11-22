-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.mem_mulR_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:40:48.285969+00:00
-- url     : https://prove2.me/submissions/6e0ada27-a4b1-47d4-8323-764d5b63a734

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution {R : Subring K} {a b : K} (hab : a * b = 1) (x : K) :
    x ∈ mulR R a ↔ b * x ∈ R := by
  unfold mulR
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have e : b * (AddMonoidHom.mulLeft a) r = r := by
      rw [AddMonoidHom.coe_mulLeft]
      linear_combination r * hab
    rw [e]
    exact hr
  · intro h
    refine ⟨b * x, h, ?_⟩
    rw [AddMonoidHom.coe_mulLeft]
    linear_combination x * hab
end Formalism.FourierDecayAlt.P.A6x4
