-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.corner_level_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:16.267218+00:00
-- url     : https://prove2.me/submissions/6784833d-93c8-41ca-9595-83dbb559b47c

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_mem_PG
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isNU_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_red_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_lift_decomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_red
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x2.coe_phi

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.KppProduct := by
  intro o _ _ r k L x
  rw [L.mem_Kpp, isNU_iff]
  constructor
  · intro hx
    obtain ⟨nb, hb, hbU, hn, hx⟩ := (mem_PG _ _).1 hx
    obtain ⟨n, κ, h, hN, rfl, hκ, rfl⟩ := lift_decomp x nb hb hn hx
    exact ⟨n, κ, h, hN, (L.mem_JH h).2 hbU, hκ, rfl⟩
  · rintro ⟨n, κ, h, hN, hh, hκ, hx⟩
    have hx' : x = n * phi o r k h * κ := Units.ext hx
    rw [hx', map_mul, MonoidHom.mem_ker.1 hκ, mul_one, map_mul, red_phi]
    exact (mem_PG _ _).2 ⟨_, _, (L.mem_JH h).1 hh, isN_red hN, rfl⟩
end Formalism.FourierDecayAlt.P
