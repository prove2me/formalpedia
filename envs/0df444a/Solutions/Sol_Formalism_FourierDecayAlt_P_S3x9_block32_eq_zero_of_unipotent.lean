-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x9.block32_eq_zero_of_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:40.356525+00:00
-- url     : https://prove2.me/submissions/b2a2041a-995d-485a-bddb-512b7b43f69a

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x9_block32_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x9_block32_levi_embedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x9
open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)
namespace Formalism.FourierDecayAlt.P.S3x9
theorem _root_.solution {A : Type} [CommRing A] {r k : ℕ} {x : Matrix (Idx r k) (Idx r k) A}
    (hx : IsNU x) : b32 x = 0 := by
  obtain ⟨n, u, hn, ⟨u', -, rfl⟩, rfl⟩ := hx
  obtain ⟨-, -, -, -, h31, h32⟩ := hn
  rw [block32_mul, h31, h32, block32_levi_embedding]
  simp
end Formalism.FourierDecayAlt.P.S3x9
