-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderIndexAndStrata.kppCorner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:08.107445+00:00
-- url     : https://prove2.me/submissions/7d03cad6-54e9-4383-a490-89c578c99103

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.OrderIndexAndStrata
theorem _root_.solution (hNU : NUExplicit) : KppCorner := by
  intro o _ _ _ ϖ hϖ r k j hj
  have h0 : b31 (j.map (IsLocalRing.residue o)) = 0 := ((hNU _ r k _).1 hj.2).2.2.2.1
  have hmax : IsLocalRing.maximalIdeal o = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hdiv : ∀ a b, ϖ ∣ b31 j a b := by
    intro a b
    have hr : IsLocalRing.residue o (b31 j a b) = 0 := by
      have := congrFun (congrFun h0 a) b
      simpa [b31] using this
    rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton] at hr
    exact hr
  choose X hX using hdiv
  exact ⟨Matrix.of X, by ext a b; simp [hX a b]⟩
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata
