-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.inGLo_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:02.335189+00:00
-- url     : https://prove2.me/submissions/d7630075-fc17-46ec-b9f8-1e5e0deec609

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
variable (o : Type) [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]
namespace Formalism.FourierDecayAlt.P.S3x3
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {x y : Matrix ι ι k0} (hx : InGLo o x)
    (hy : InGLo o y) : InGLo o (x * y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, by rw [Matrix.det_mul]; exact ha.mul hb, by rw [Matrix.map_mul]⟩
end Formalism.FourierDecayAlt.P.S3x3
