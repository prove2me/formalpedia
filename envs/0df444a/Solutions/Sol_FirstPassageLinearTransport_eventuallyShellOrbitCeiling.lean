-- Prove2me | solution 1 for FirstPassageLinearTransport.eventuallyShellOrbitCeiling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:17:25.048261+00:00
-- url     : https://prove2.me/submissions/77d84e60-8749-403a-abaa-ea3fe0a33a45

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_orbit_le_stageClock_ceiling
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_eventuallyLogAddRpowLe
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageCount_le
import Theorems.Thm_FirstPassageLinearTransport_stageK_one_le
import Theorems.Thm_FirstPassageLinearTransport_stageK_pos
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta omega beta : ℝ} (p : StageSetup r eta)
    (homega : 0 < omega) (hetaBeta : eta < beta) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      ∀ j : ℕ, j ≤ stageClock p (stageCount omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  let A := 2 * omega * Real.log (stageK p)
  let c := (beta - eta) * Real.log 2 / 2
  have hlogK0 : 0 ≤ Real.log (stageK p) :=
    Real.log_nonneg (stageK_one_le p)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos
      (mul_pos (sub_pos.mpr hetaBeta) (Real.log_pos (by norm_num)))
      (by norm_num)
  have hscalarReal := eventuallyLogAddRpowLe
    (A := A) (C := 0) (c := c) (a := (1 / 2 : ℝ)) (delta := 0)
    hA (by norm_num) hc (by norm_num) (by norm_num)
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hscalar := hxT.eventually hscalarReal
  filter_upwards [hscalar, eventually_ge_atTop (4 : ℕ)] with M hsc hM
  intro n hn hnshell hnboot j hj
  let R := stageCount omega M
  let x : ℝ := (M : ℝ) + 4
  have hx : 0 < x := by dsimp [x]; positivity
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by dsimp [x]; linarith)
  have hsc' : A * Real.log x ≤ c * x := by
    simpa [x] using hsc
  have hxM : x ≤ 2 * (M : ℝ) := by
    dsimp [x]
    exact_mod_cast (by omega : M + 4 ≤ 2 * M)
  have hlinear : A * Real.log x ≤
      (beta - eta) * (M : ℝ) * Real.log 2 := by
    calc
      A * Real.log x ≤ c * x := hsc'
      _ ≤ c * (2 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hxM hc.le
      _ = (beta - eta) * (M : ℝ) * Real.log 2 := by
        dsimp [c]
        ring
  have hR := stageCount_le homega.le M
  have hRlog : (2 * R : ℕ) * Real.log (stageK p) ≤
      A * Real.log x := by
    have htwoLogK : 0 ≤ 2 * Real.log (stageK p) :=
      mul_nonneg (by norm_num) hlogK0
    have hmul := mul_le_mul_of_nonneg_right hR htwoLogK
    dsimp [R, A, x] at hmul ⊢
    push_cast at hmul ⊢
    nlinarith
  have hlowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnshell).1
  have hlowerCast : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast hlowerNat
  have hlogLower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
      hlowerCast
    rw [Real.log_pow] at h
    exact h
  have hmargin : 0 ≤ beta - eta := sub_nonneg.mpr hetaBeta.le
  have hexponent : (2 * R : ℕ) * Real.log (stageK p) ≤
      (beta - eta) * Real.log n := by
    calc
      (2 * R : ℕ) * Real.log (stageK p) ≤ A * Real.log x := hRlog
      _ ≤ (beta - eta) * (M : ℝ) * Real.log 2 := hlinear
      _ ≤ (beta - eta) * Real.log n := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hlogLower hmargin)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfactor : stageK p ^ (2 * R) ≤ (n : ℝ) ^ (beta - eta) := by
    rw [← Real.exp_log (pow_pos (stageK_pos p) (2 * R)), Real.log_pow,
      Real.rpow_def_of_pos hnR]
    apply Real.exp_le_exp.2
    push_cast
    simpa [mul_comm] using hexponent
  have hpath := orbit_le_stageClock_ceiling p hn hnboot hj
  calc
    (orbit j n : ℝ) ≤
        stageK p ^ (2 * R) * (n : ℝ) ^ (1 + eta) := hpath
    _ ≤ (n : ℝ) ^ (beta - eta) * (n : ℝ) ^ (1 + eta) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ (1 + beta) := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring
end FirstPassageLinearTransport
