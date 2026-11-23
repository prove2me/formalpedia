-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.inGLo_hEmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:58.481321+00:00
-- url     : https://prove2.me/submissions/6eea3da4-cafc-46af-b776-3e242b3efb62

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_det_hEmb
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_hEmb_map

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
theorem _root_.solution {r k : ℕ} {h : Matrix (Fin k) (Fin k) k0} (hh : InGLo o h) :
    InGLo o (hEmb r h) := by
  obtain ⟨a, ha, rfl⟩ := hh
  exact ⟨hEmb r a, by rw [det_hEmb]; exact ha, hEmb_map _ _⟩
end Formalism.FourierDecayAlt.P.S3x3
