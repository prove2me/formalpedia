-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.conj_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:39.879951+00:00
-- url     : https://prove2.me/submissions/a43c64fd-e97f-449e-b921-818e53a712d1

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
section
noncomputable section
open Matrix
namespace Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
private theorem mul_eq_one_comm_of_mul_eq_one {G G' : Matrix ι ι K} (h : G * G' = 1) : G' * G = 1 :=
  mul_eq_one_comm.mp h
end Formalism.L2.SG.Pf.Unip
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution {G G' Z : Matrix ι ι K} (h : G * G' = 1) (j : ℕ) : G' * Z ^ j * G = (G' * Z * G) ^ j := by
  have hG : G' * G = 1 := mul_eq_one_comm_of_mul_eq_one h
  induction j with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hG]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G G', h, Matrix.one_mul]
end Formalism.L2.SG.Pf.Unip
