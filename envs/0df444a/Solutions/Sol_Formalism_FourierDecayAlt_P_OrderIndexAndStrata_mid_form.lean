-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderIndexAndStrata.mid_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:18.456602+00:00
-- url     : https://prove2.me/submissions/3b1d3c2c-07b8-4df7-a485-20f757504395

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
theorem _root_.solution {A : Type} [CommRing A] {k : ℕ} (y : Matrix (Mid k) (Mid k) A) (hy : IsUnit y.det)
    (c22 : ∀ a, y a (Sum.inr ()) = if a = Sum.inr () then 1 else 0)
    (r22 : ∀ b, y (Sum.inr ()) b = if b = Sum.inr () then 1 else 0) :
    ∃ h, IsUnit h.det ∧ y = midEmb h := by
  have hy' : y = midEmb (Matrix.of fun a b => y (Sum.inl a) (Sum.inl b)) := by
    ext (a | ⟨⟩) (b | ⟨⟩)
    · simp [midEmb]
    · simpa [midEmb] using c22 (Sum.inl a)
    · simpa [midEmb] using r22 (Sum.inl b)
    · simpa [midEmb] using c22 (Sum.inr ())
  refine ⟨_, ?_, hy'⟩
  rw [hy', Formalism.FourierDecayAlt.P.S3x1.midEmb_det] at hy
  exact hy
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata
