-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.natural_level_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:30.836687+00:00
-- url     : https://prove2.me/submissions/41d1a9f9-0c9c-4cdd-8892-2e3c233052eb

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_mem_PG
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isS_iff
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
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.KnatProduct := by
  intro o _ _ r k L x
  rw [L.mem_Knat, isS_iff]
  constructor
  · intro hx
    obtain ⟨nb, hb, -, hn, hx⟩ := (mem_PG _ _).1 hx
    obtain ⟨n, κ, h, hN, -, hκ, rfl⟩ := lift_decomp x nb hb hn hx
    exact ⟨n * phi o r k h, κ, (isS_iff _).2 ((mem_PG _ _).2 ⟨n, h, Subgroup.mem_top _, hN, rfl⟩),
      hκ, rfl⟩
  · rintro ⟨s, κ, hs, hκ, rfl⟩
    obtain ⟨n, h, -, hN, rfl⟩ := (mem_PG _ _).1 ((isS_iff _).1 hs)
    rw [map_mul, MonoidHom.mem_ker.1 hκ, mul_one, map_mul, red_phi]
    exact (mem_PG _ _).2 ⟨_, _, Subgroup.mem_top _, isN_red hN, rfl⟩
end Formalism.FourierDecayAlt.P
