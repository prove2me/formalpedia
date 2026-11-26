-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapLogBoundScheduleLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:14.172074+00:00
-- url     : https://prove2.me/submissions/5f8d2970-0a9c-4552-8b9e-b4bcef056f82

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_extendedWindow_powerDense
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_pullbackShellConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageCount_le
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta chi Dc omega : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (homega0 : 0 ≤ omega) (M : ℕ) :
    bootstrapLogBound p chi Dc (stageCount omega M) ≤
      bootstrapScheduleA p chi Dc omega *
        (Real.log ((M : ℝ) + 4) + 1) ^ 2 := by
  let x := Real.log ((M : ℝ) + 4)
  let R : ℝ := stageCount omega M
  let b0 := Real.log (quadraticWindowGlobalConstant eta + 2)
  let b1 := Real.log (bootstrapStageK p chi Dc)
  let b2 := Real.log Dc⁻¹
  let b3 := Real.log chi⁻¹
  have hx0 : 0 ≤ x := by
    dsimp [x]
    apply Real.log_nonneg
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR : R ≤ omega * x := by
    dsimp [R, x]
    exact stageCount_le homega0 M
  have hb0 : 0 ≤ b0 := by
    dsimp [b0]
    apply Real.log_nonneg
    linarith [(extendedWindow_powerDense p).C_pos]
  have hb1 : 0 ≤ b1 := by
    dsimp [b1]
    apply Real.log_nonneg
    unfold bootstrapStageK
    have hK : 0 < pullbackGlobalConstant p chi Dc := by
      have hnum : 0 < 2 * pullbackShellConstant p chi Dc :=
        mul_pos (by norm_num) (pullbackShellConstant_pos p hchir)
      have hden : 0 < 2 * Real.exp (-(chi * Dc * Real.log 2)) - 1 := by
        have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        have hchiDc : chi * Dc < 1 := by
          have hprod : chi * Dc ≤ chi * 1 :=
            mul_le_mul_of_nonneg_left hDc1 hchi0.le
          nlinarith [hchir.trans p.r_lt_one]
        have harg : -Real.log 2 < -(chi * Dc * Real.log 2) := by
          nlinarith
        have hexp := Real.exp_lt_exp.2 harg
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
        nlinarith
      simpa [pullbackGlobalConstant] using div_pos hnum hden
    linarith
  have hb2 : 0 ≤ b2 := by
    dsimp [b2]
    exact Real.log_nonneg ((one_le_inv₀ hDc0).2 hDc1)
  have hb3 : 0 ≤ b3 := by
    dsimp [b3]
    exact Real.log_nonneg ((one_le_inv₀ hchi0).2 hchi1)
  have hR2 : R ^ 2 ≤ (omega * x) ^ 2 := by nlinarith
  have hraw : b0 + R * b1 + 2 * R * b2 + 2 * R ^ 2 * b3 ≤
      b0 + (omega * x) * b1 + 2 * (omega * x) * b2 +
        2 * (omega * x) ^ 2 * b3 := by
    gcongr
  have hx1 : 1 ≤ (x + 1) ^ 2 := by nlinarith
  have hxx : x ≤ (x + 1) ^ 2 := by nlinarith
  have hxx2 : x ^ 2 ≤ (x + 1) ^ 2 := by nlinarith
  dsimp [bootstrapLogBound, bootstrapScheduleA, x, R, b0, b1, b2, b3]
    at hraw ⊢
  calc
    _ ≤ Real.log (quadraticWindowGlobalConstant eta + 2) +
        (omega * Real.log ((M : ℝ) + 4)) *
          Real.log (bootstrapStageK p chi Dc) +
        2 * (omega * Real.log ((M : ℝ) + 4)) * Real.log Dc⁻¹ +
        2 * (omega * Real.log ((M : ℝ) + 4)) ^ 2 *
          Real.log chi⁻¹ := hraw
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left hx1 hb0,
        mul_le_mul_of_nonneg_left hxx (mul_nonneg homega0 hb1),
        mul_le_mul_of_nonneg_left hxx (mul_nonneg homega0 hb2),
        mul_le_mul_of_nonneg_left hxx2
          (mul_nonneg (sq_nonneg omega) hb3)]
end FirstPassageLinearTransport
