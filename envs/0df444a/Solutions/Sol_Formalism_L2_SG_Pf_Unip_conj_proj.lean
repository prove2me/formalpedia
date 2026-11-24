-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.conj_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:33.517538+00:00
-- url     : https://prove2.me/submissions/ee210203-52bb-4f91-9a8a-98beec62fd54

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RCocompactPfConj
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_conj_sharp

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution [Invertible (2 : K)] {J J' G G' A : Matrix ι ι K} (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J')
    (hJ : J' * J = 1) (hJ' : J * J' = 1) (hG : Gᴴ * J * G = J) (h : G * G' = 1) :
    G' * proj J J' A * G = proj J J' (G' * A * G) := by
  unfold proj
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, conj_sharp hJh hJ'h hJ hJ' hG h]
end Formalism.L2.SG.Pf.Unip
