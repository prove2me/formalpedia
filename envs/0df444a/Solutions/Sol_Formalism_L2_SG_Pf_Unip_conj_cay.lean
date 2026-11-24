-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.conj_cay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:40:06.414268+00:00
-- url     : https://prove2.me/submissions/68e7f7b7-8382-4e99-9756-efba31cc6e52

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RCocompactPfConj
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_conj_geo
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
theorem _root_.solution [Invertible (2 : K)] {G G' Z : Matrix ι ι K} (h : G * G' = 1) (N : ℕ) :
    G' * cay N Z * G = cay N (G' * Z * G) := by
  have hG : G' * G = 1 := mul_eq_one_comm_of_mul_eq_one h
  have e1 : G' * ((⅟2 : K) • Z) * G = (⅟2 : K) • (G' * Z * G) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  unfold cay
  rw [← e1, ← conj_geo h, mul_add, add_mul, Matrix.mul_one, hG]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G G', h, Matrix.one_mul]
end Formalism.L2.SG.Pf.Unip
