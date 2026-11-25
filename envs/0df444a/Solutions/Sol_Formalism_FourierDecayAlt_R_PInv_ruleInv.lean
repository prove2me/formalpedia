-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.PInv.ruleInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:54.617921+00:00
-- url     : https://prove2.me/submissions/3126a719-0db0-4c10-a2a1-b99efbfd385a

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_fcomm
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_cb
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_cbi
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_c
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_ci
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem___78c8e7adc78b
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__i_46b19cb3119f
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__b_d9e4f796149b
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__bi_b985a748edca
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_GG
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_GGi
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_comm_ofFn
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_comm_Tprod
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_comm_Tvprod
import Theorems.Thm_Formalism_FourierDecayAlt_R_PInv_comm_alg
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_hR_bar
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_hR_hol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.R.PInv
theorem _root_.solution : RuleInv := by
  intro A _ _ r L Y

  have zb_p : ∀ l, Commute L.ζbi (L.p l) := fun l => (L.p_ζbi l).symm
  have zb_pb : ∀ l, Commute L.ζbi (L.pb l) := fun l => (L.pb_ζbi l).symm
  have z_p : ∀ l, Commute L.ζi (L.p l) := fun l => (L.p_ζi l).symm
  have z_pb : ∀ l, Commute L.ζi (L.pb l) := fun l => (L.pb_ζi l).symm
  have fc := fun {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) => L.inv_fcomm hx hy
  have zbAr : ∀ i j, Commute L.ζbi (L.Tprod Y i j) :=
    L.inv_comm_Tprod zb_p (fun l => fc L.inv_mem_ζbi (L.inv_mem_c l)) (fun l => fc L.inv_mem_ζbi (L.inv_mem_ci l)) Y
  have zbAv : ∀ i j, Commute L.ζbi (L.Tvprod Y i j) :=
    L.inv_comm_Tvprod zb_pb (fun l => fc L.inv_mem_ζbi (L.inv_mem_cb l)) (fun l => fc L.inv_mem_ζbi (L.inv_mem_cbi l)) Y
  have zAr : ∀ i j, Commute L.ζi (L.Tprod Y i j) :=
    L.inv_comm_Tprod z_p (fun l => fc L.inv_mem_ζi (L.inv_mem_c l)) (fun l => fc L.inv_mem_ζi (L.inv_mem_ci l)) Y
  have zAv : ∀ i j, Commute L.ζi (L.Tvprod Y i j) :=
    L.inv_comm_Tvprod z_pb (fun l => fc L.inv_mem_ζi (L.inv_mem_cb l)) (fun l => fc L.inv_mem_ζi (L.inv_mem_cbi l)) Y
  have zbDr : Commute L.ζbi L.Dr := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζbi (L.inv_mem_c l)
  have zbDrb : Commute L.ζbi L.Drb := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζbi (L.inv_mem_cb l)
  have zDr : Commute L.ζi L.Dr := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζi (L.inv_mem_c l)
  have zDrb : Commute L.ζi L.Drb := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζi (L.inv_mem_cb l)
  have zbGG : Commute L.ζbi L.GG := fc L.inv_mem_ζbi L.inv_mem_GG
  have zGG : Commute L.ζi L.GG := fc L.inv_mem_ζi L.inv_mem_GG
  have zb_l0 : Commute L.ζbi (L.l0 Y) := by
    simp only [LevelData.l0]
    exact ((show Commute L.ζbi L.nab from L.nab_ζbi.symm).neg_right).sub_right ((comm_alg _ _).mul_right
      ((fc L.inv_mem_ζbi L.inv_mem_ζb).mul_right (fc L.inv_mem_ζbi L.inv_mem_GGi)))
  have z_m0 : Commute L.ζi (L.m0 Y) := by
    simp only [LevelData.m0]
    exact ((show Commute L.ζi L.nabs from L.nabs_ζi.symm).neg_right).sub_right ((comm_alg _ _).mul_right
      ((fc L.inv_mem_ζi L.inv_mem_ζ).mul_right (fc L.inv_mem_ζi L.inv_mem_GGi)))
  have hm : L.m0 Y * L.ζbi = L.ζbi * L.m0 Y - L.ζbi * L.ζbi := by
    have hX : Commute L.ζbi (algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) :=
      (comm_alg _ _).mul_right ((fc L.inv_mem_ζbi L.inv_mem_ζ).mul_right (fc L.inv_mem_ζbi L.inv_mem_GGi))
    simp only [LevelData.m0]
    calc (-L.nabs - algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) * L.ζbi
        = -(L.nabs * L.ζbi) - algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi) * L.ζbi := by noncomm_ring
      _ = -(L.ζbi * L.nabs + L.ζbi * L.ζbi) - L.ζbi * (algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) := by
          rw [L.nabs_ζbi, hX.eq]
      _ = _ := by noncomm_ring
  have hl : L.l0 Y * L.ζi = L.ζi * L.l0 Y + L.ζi * L.ζi := by
    have hX : Commute L.ζi (algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) :=
      (comm_alg _ _).mul_right ((fc L.inv_mem_ζi L.inv_mem_ζb).mul_right (fc L.inv_mem_ζi L.inv_mem_GGi))
    simp only [LevelData.l0]
    calc (-L.nab - algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) * L.ζi
        = -(L.nab * L.ζi) - algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi) * L.ζi := by noncomm_ring
      _ = -(L.ζi * L.nab - L.ζi * L.ζi) - L.ζi * (algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) := by
          rw [L.nab_ζi, hX.eq]
      _ = _ := by noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (zbDr.mul_right (zbAr 0 0)).eq
  · exact ((zbDrb.mul_right zbGG).mul_right ((zb_l0.mul_right (zbAr 0 0)).add_right (zbAr 1 0))).eq
  · exact (zbDrb.mul_right (zbAv 0 0)).eq
  · rw [inv_hR_bar]
    have e1 : (L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi
        = (L.ζbi * L.m0 Y - L.ζbi * L.ζbi) * L.Avr Y + L.ζbi * L.Bvr Y := by
      have hA1 : Commute L.ζbi (L.Avr Y) := zbAv 0 0
      have hB1 : Commute L.ζbi (L.Bvr Y) := zbAv 1 0
      rw [add_mul, mul_assoc, ← hA1.eq, ← mul_assoc, hm, ← hB1.eq]
    have hDG : Commute L.ζbi (L.Dr * L.GG) := zbDr.mul_right zbGG
    simp only [LevelData.R0v]
    calc L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi - L.ζbi * (L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y))
        = L.Dr * L.GG * ((L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi) - (L.ζbi * (L.Dr * L.GG)) * (L.m0 Y * L.Avr Y + L.Bvr Y) := by
          noncomm_ring
      _ = L.Dr * L.GG * ((L.ζbi * L.m0 Y - L.ζbi * L.ζbi) * L.Avr Y + L.ζbi * L.Bvr Y) - (L.Dr * L.GG * L.ζbi) * (L.m0 Y * L.Avr Y + L.Bvr Y) := by
          rw [e1, hDG.eq]
      _ = _ := by noncomm_ring
  · exact (zDr.mul_right (zAr 0 0)).eq
  · exact (zDrb.mul_right (zAv 0 0)).eq
  · exact ((zDr.mul_right zGG).mul_right ((z_m0.mul_right (zAv 0 0)).add_right (zAv 1 0))).eq
  · rw [inv_hR_hol]
    have e1 : (L.l0 Y * L.Ar Y + L.Br Y) * L.ζi
        = (L.ζi * L.l0 Y + L.ζi * L.ζi) * L.Ar Y + L.ζi * L.Br Y := by
      have hA1 : Commute L.ζi (L.Ar Y) := zAr 0 0
      have hB1 : Commute L.ζi (L.Br Y) := zAr 1 0
      rw [add_mul, mul_assoc, ← hA1.eq, ← mul_assoc, hl, ← hB1.eq]
    have hDG : Commute L.ζi (L.Drb * L.GG) := zDrb.mul_right zGG
    simp only [LevelData.R0]
    calc L.Drb * L.GG * (L.l0 Y * L.Ar Y + L.Br Y) * L.ζi - L.ζi * (L.Drb * L.GG * (L.l0 Y * L.Ar Y + L.Br Y))
        = L.Drb * L.GG * ((L.l0 Y * L.Ar Y + L.Br Y) * L.ζi) - (L.ζi * (L.Drb * L.GG)) * (L.l0 Y * L.Ar Y + L.Br Y) := by
          noncomm_ring
      _ = L.Drb * L.GG * ((L.ζi * L.l0 Y + L.ζi * L.ζi) * L.Ar Y + L.ζi * L.Br Y) - (L.Drb * L.GG * L.ζi) * (L.l0 Y * L.Ar Y + L.Br Y) := by
          rw [e1, hDG.eq]
      _ = _ := by noncomm_ring
end Formalism.FourierDecayAlt.R.PInv
