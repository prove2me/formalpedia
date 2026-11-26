-- Prove2me | solution 1 for FirstPassageLinearTransport.eventuallyShellLanding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:03.64626+00:00
-- url     : https://prove2.me/submissions/340966e1-41c0-4f99-bfca-9504ceefdc6a

import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
import Definitions.Def_FirstPassageLinearTransport_StretchedLogLanding
import Theorems.Thm_FirstPassageLinearTransport_eventuallyLogAddRpowLe
import Theorems.Thm_FirstPassageLinearTransport_stageCountRpowUpper
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageCount_le
import Theorems.Thm_FirstPassageLinearTransport_stageK_one_le
import Theorems.Thm_FirstPassageLinearTransport_stageK_pos
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_le_power
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
    {r eta omega delta : ℝ} (p : StageSetup r eta)
    (homega0 : 0 < omega) (hdelta1 : delta < 1)
    (hdescent : delta < descentAlpha omega r) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      (stageOrbit p (stageCount omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta)) := by
  let a := descentAlpha omega r
  let A := omega * Real.log (stageK p)
  let C := r⁻¹ * Real.log 2
  let c := (Real.log 2 / 5) ^ (1 - delta)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg homega0.le
      (Real.log_nonneg (stageK_one_le p))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (inv_nonneg.mpr p.r_pos.le)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hc : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hscalarReal := eventuallyLogAddRpowLe hA hC hc
    hdelta1 hdescent
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop (4 : ℝ)
      tendsto_natCast_atTop_atTop
  have hscalar : ∀ᶠ M : ℕ in atTop,
      A * Real.log ((M : ℝ) + 4) +
          C * ((M : ℝ) + 4) ^ (1 - a) ≤
        c * ((M : ℝ) + 4) ^ (1 - delta) :=
    hxT.eventually hscalarReal
  filter_upwards [hscalar, eventually_ge_atTop (1 : ℕ)] with M hsc hM
  intro n hn hnshell hnboot
  let R := stageCount omega M
  let x : ℝ := (M : ℝ) + 4
  have hx : 0 < x := by dsimp [x]; positivity
  have hstage := stageOrbit_le_power p hn hnboot
  have hRle := stageCount_le homega0.le M
  have hlogK0 : 0 ≤ Real.log (stageK p) :=
    Real.log_nonneg (stageK_one_le p)
  have hstartup : (R : ℝ) * Real.log (stageK p) ≤
      A * Real.log x := by
    dsimp [R, A, x]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hRle hlogK0
  have hrpow := stageCountRpowUpper (omega := omega)
    p.r_pos p.r_lt_one M
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hnupper : (n : ℝ) < (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast (mem_dyadicShell.mp hnshell).2
  have hlognUpper : Real.log n ≤ ((M : ℝ) + 1) * Real.log 2 := by
    have h := Real.log_le_log (by exact_mod_cast hn) hnupper.le
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hMx : (M : ℝ) + 1 ≤ x := by dsimp [x]; linarith
  have htail : (r ^ R : ℝ) * Real.log n ≤
      C * x ^ (1 - a) := by
    have hrhs0 : 0 ≤ r⁻¹ * ((M : ℝ) + 4) ^
        (-descentAlpha omega r) :=
      mul_nonneg (inv_nonneg.mpr p.r_pos.le)
        (Real.rpow_nonneg (by positivity) _)
    have h1 := mul_le_mul hrpow hlognUpper hlogn0 hrhs0
    have h2 : r⁻¹ * x ^ (-a) * (((M : ℝ) + 1) * Real.log 2) ≤
        r⁻¹ * Real.log 2 * x ^ (1 - a) := by
      have hxm := mul_le_mul_of_nonneg_right hMx
        (mul_nonneg (inv_nonneg.mpr p.r_pos.le)
          (Real.rpow_nonneg hx.le (-a)))
      have hid : r⁻¹ * x ^ (-a) * (x * Real.log 2) =
          r⁻¹ * Real.log 2 * x ^ (1 - a) := by
        rw [show (1 : ℝ) - a = 1 + (-a) by ring,
          Real.rpow_add hx, Real.rpow_one]
        ring
      calc
        r⁻¹ * x ^ (-a) * (((M : ℝ) + 1) * Real.log 2)
            = (((M : ℝ) + 1) * (r⁻¹ * x ^ (-a))) *
                Real.log 2 := by ring
        _ ≤ (x * (r⁻¹ * x ^ (-a))) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hxm
            (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
        _ = r⁻¹ * x ^ (-a) * (x * Real.log 2) := by ring
        _ = r⁻¹ * Real.log 2 * x ^ (1 - a) := hid
    exact h1.trans h2
  have hexponent : (R : ℝ) * Real.log (stageK p) +
      (r ^ R : ℝ) * Real.log n ≤
        c * x ^ (1 - delta) := by
    dsimp [A, C, a, c, x] at hsc ⊢
    exact (add_le_add hstartup htail).trans hsc
  have htargetBase : Real.log 2 / 5 * x ≤ Real.log n := by
    have hfrac : x / 5 ≤ (M : ℝ) := by
      dsimp [x]
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hlowerNat : (2 : ℕ) ^ M ≤ n :=
      (mem_dyadicShell.mp hnshell).1
    have hlower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
      have hlowerCast : (2 : ℝ) ^ M ≤ (n : ℝ) := by
        exact_mod_cast hlowerNat
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
        hlowerCast
      rw [Real.log_pow] at h
      exact h
    nlinarith [mul_le_mul_of_nonneg_right hfrac
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
  have htarget : c * x ^ (1 - delta) ≤
      (Real.log n) ^ (1 - delta) := by
    have hpow := Real.rpow_le_rpow
      (by positivity : (0 : ℝ) ≤ Real.log 2 / 5 * x)
      htargetBase (sub_pos.mpr hdelta1).le
    have hmul : (Real.log 2 / 5 * x) ^ (1 - delta) =
        c * x ^ (1 - delta) := by
      rw [Real.mul_rpow (by positivity : 0 ≤ Real.log 2 / 5) hx.le]
    rw [← hmul]
    exact hpow
  have hprod : stageK p ^ R * (n : ℝ) ^ (r ^ R) =
      Real.exp ((R : ℝ) * Real.log (stageK p) +
        (r ^ R : ℝ) * Real.log n) := by
    rw [Real.exp_add, Real.rpow_def_of_pos (by exact_mod_cast hn)]
    congr 1
    · rw [← Real.exp_log (pow_pos (stageK_pos p) R), Real.log_pow]
    · congr 1
      ring
  calc
    (stageOrbit p R n : ℝ) ≤
        stageK p ^ R * (n : ℝ) ^ (r ^ R) := hstage
    _ = Real.exp ((R : ℝ) * Real.log (stageK p) +
        (r ^ R : ℝ) * Real.log n) := hprod
    _ ≤ Real.exp (c * x ^ (1 - delta)) :=
      Real.exp_le_exp.2 hexponent
    _ ≤ Real.exp ((Real.log n) ^ (1 - delta)) :=
      Real.exp_le_exp.2 htarget
end FirstPassageLinearTransport
