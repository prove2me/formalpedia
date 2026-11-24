-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcCut.nc_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:37:43.94722+00:00
-- url     : https://prove2.me/submissions/b115e0ff-dfc7-449e-af9f-a83bd3815185

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NormalizingConstantEq
import Theorems.Thm_Formalism_L2_SG_Pf_NcCut_normalizing_constant_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcCut
open Formalism.FourierDecayAlt.S3
variable {P : Type} [Fintype P] (B : MassData P)
namespace Formalism.L2.SG.Pf.NcCut
theorem _root_.solution (hP : B.Pos) (hM : B.InMass) (hMs : B.InMasses) (hL : B.InLevelS) (hO : B.InOrdinary)
    (hT : B.InTyped) (hV : B.volNa = 1 ∧ B.volNa' = 1) (c ng kap : ℝ) (hkap : kap ≠ 0) :
    c = B.n0c * ng / (B.al * kap) ↔
      c * B.al * kap = B.volB / B.volHa * B.Coo * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) *
        B.μKnat / B.μH' * ng := by
  rw [normalizing_constant_eq B hP hM hMs hL hO hT hV]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hal, -⟩ := hP
  rw [eq_div_iff (mul_ne_zero hal.ne' hkap)]
  constructor <;> intro h <;> linear_combination h
end Formalism.L2.SG.Pf.NcCut
