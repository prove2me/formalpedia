-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.div_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:11:38.139038+00:00
-- url     : https://prove2.me/submissions/05b910dc-e3ad-477a-9e54-8adbe8389081

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]
variable [IsDomain o] [IsDiscreteValuationRing o]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {ϖ : o} (hϖ : Irreducible ϖ) {m n : Type} (x : Matrix m n o)
    (h : x.map (IsLocalRing.residue o) = 0) : ∃ y : Matrix m n o, x = ϖ • y := by
  have : ∀ a b, ∃ c, x a b = ϖ * c := fun a b => by
    have h1 : IsLocalRing.residue o (x a b) = 0 := congrFun (congrFun h a) b
    rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    exact h1
  choose y hy using this
  exact ⟨Matrix.of y, by ext a b; simp [hy]⟩
end Formalism.FourierDecayAlt.P.S3x8
