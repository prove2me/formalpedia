-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_polylogTerminalRank_lt_shrinkingSwitchRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:45.855127+00:00
-- url     : https://prove2.me/submissions/7c0431a1-e5da-4ae3-8488-81151f3a9a5d

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lower
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_polylogTerminalRank_lt_add_one
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A C : ℝ} (hA : 0 ≤ A)
    (hAC : A / Real.log 2 < C) :
    ∀ᶠ M : ℕ in atTop,
      polylogTerminalRank A M < shrinkingSwitchRank C M := by
  let g := C - A / Real.log 2
  have hg : 0 < g := by dsimp [g]; linarith
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hlogT : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 2))
      atTop atTop := Real.tendsto_log_atTop.comp hxT
  have hlarge : ∀ᶠ M : ℕ in atTop,
      1 < g * Real.log ((M : ℝ) + 2) := by
    have hmul := hlogT.const_mul_atTop hg
    filter_upwards [(tendsto_atTop.1 hmul) 2] with M hM
    linarith
  filter_upwards [hlarge] with M hlarge
  have hterminal := polylogTerminalRank_lt_add_one hA M
  have hswitch := shrinkingSwitchRank_lower C M
  have hrewrite :
      A * Real.logb 2 ((M : ℝ) + 2) =
        (A / Real.log 2) * Real.log ((M : ℝ) + 2) := by
    simp [Real.logb]
    ring
  have hreal :
      (polylogTerminalRank A M : ℝ) <
        (shrinkingSwitchRank C M : ℝ) := by
    calc
      (polylogTerminalRank A M : ℝ) <
          A * Real.logb 2 ((M : ℝ) + 2) + 1 := hterminal
      _ = (A / Real.log 2) * Real.log ((M : ℝ) + 2) + 1 := by
        rw [hrewrite]
      _ < C * Real.log ((M : ℝ) + 2) := by
        dsimp [g] at hlarge
        nlinarith
      _ ≤ (shrinkingSwitchRank C M : ℝ) := hswitch
  exact_mod_cast hreal
end FirstPassageLinearTransport
