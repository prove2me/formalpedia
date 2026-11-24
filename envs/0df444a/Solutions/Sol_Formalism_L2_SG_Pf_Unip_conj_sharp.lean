-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.conj_sharp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:40.851444+00:00
-- url     : https://prove2.me/submissions/f92d8708-2b52-4b90-a8ad-a4ea7ead109f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RCocompactPfConj

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
theorem _root_.solution {J J' G G' A : Matrix ι ι K} (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J') (hJ : J' * J = 1) (hJ' : J * J' = 1)
    (hG : Gᴴ * J * G = J) (h : G * G' = 1) : G' * sharp J J' A * G = sharp J J' (G' * A * G) := by
  have key : G' = J' * Gᴴ * J := by
    calc G' = (J' * (Gᴴ * J * G)) * G' := by rw [hG, hJ, Matrix.one_mul]
      _ = J' * Gᴴ * J * (G * G') := by simp only [Matrix.mul_assoc]
      _ = J' * Gᴴ * J := by rw [h, Matrix.mul_one]
  have key' : G'ᴴ = J * (G * J') := by
    rw [key]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJh, hJ'h, Matrix.mul_assoc]
  unfold sharp
  rw [conjTranspose_mul, conjTranspose_mul, key']
  rw [key]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc J J', hJ', Matrix.one_mul, hJ, Matrix.mul_one]
end Formalism.L2.SG.Pf.Unip
