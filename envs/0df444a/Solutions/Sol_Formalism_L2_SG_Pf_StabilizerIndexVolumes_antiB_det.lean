-- Prove2me | solution 1 for Formalism.L2.SG.Pf.StabilizerIndexVolumes.antiB_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:44:27.430707+00:00
-- url     : https://prove2.me/submissions/b05cb092-7901-4639-a60c-39250c5da4ba

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_StabilizerIndexVolumes_PtMatIsUnit
import Theorems.Thm_Formalism_L2_SG_Pf_StabilizerIndexVolumes_antiB_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StabilizerIndexVolumes
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes
theorem _root_.solution (t : K) (ht : t ≠ 0) (s : ℕ) : (antiB t s).det ≠ 0 := by
  intro h
  have h2 := congrArg Matrix.det (antiB_sq t s)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin] at h2
  exact pow_ne_zero s (mul_ne_zero ht ht) h2.symm
end Formalism.L2.SG.Pf.StabilizerIndexVolumes
