-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_dyadic_rank_term_le_endpoint_entropy_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:31.490251+00:00
-- url     : https://prove2.me/submissions/b19a1bd3-bc55-4071-8324-8b58a54e9630

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeSupportScalars
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_lt_logTwo
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_pos
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∀ᶠ L : ℕ in atTop,
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) ≤
        Real.sqrt L *
          Real.exp (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) := by
  let gap := Real.log 2 - firstPassageEndpointRate
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr firstPassageEndpointRate_lt_logTwo
  have hreal := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (1 / 2 : ℝ) gap hgap
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  have hsmall := hnat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with L hsmall hL
  have hLR : 0 < (L : ℝ) := by positivity
  have hroot : Real.sqrt (L : ℝ) = (L : ℝ) ^ (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow _
  have hsmall' :
      (L : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-(gap * (L : ℝ))) < 1 / 2 := by
    simpa [Function.comp_def] using hsmall
  have hfactor :
      2 * Real.sqrt L * Real.exp (-(gap * (L : ℝ))) ≤ 1 := by
    rw [hroot]
    linarith
  have hlin : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by
    exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  have hsqrtSq : Real.sqrt L * Real.sqrt L = (L : ℝ) := by
    convert Real.sq_sqrt (show (0 : ℝ) ≤ L by positivity) using 1 <;> ring
  have hsplit :
      Real.exp (-(Real.log 2 * (L : ℝ))) =
        Real.exp (-(gap * (L : ℝ))) *
          Real.exp (-(firstPassageEndpointRate * (L : ℝ))) := by
    rw [← Real.exp_add]
    dsimp [gap]
    congr 1
    ring
  have hshift :
      Real.exp (-(firstPassageEndpointRate * (L : ℝ))) ≤
        Real.exp (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hsub : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L 1
    nlinarith [firstPassageEndpointRate_pos]
  calc
    ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) ≤
        (2 * (L : ℝ)) * Real.exp (-(Real.log 2 * (L : ℝ))) := by
      gcongr
    _ = (2 * Real.sqrt L * Real.exp (-(gap * (L : ℝ)))) *
        (Real.sqrt L * Real.exp
          (-(firstPassageEndpointRate * (L : ℝ)))) := by
      rw [hsplit]
      calc
        (2 * (L : ℝ)) *
            (Real.exp (-(gap * (L : ℝ))) *
              Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) =
            (2 * (Real.sqrt L * Real.sqrt L)) *
              (Real.exp (-(gap * (L : ℝ))) *
                Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) := by
                  rw [hsqrtSq]
        _ = _ := by ring
    _ ≤ 1 * (Real.sqrt L * Real.exp
          (-(firstPassageEndpointRate * (L : ℝ)))) := by
      gcongr
    _ ≤ Real.sqrt L *
        Real.exp (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) := by
      simpa using mul_le_mul_of_nonneg_left hshift (Real.sqrt_nonneg _)
end FirstPassageLinearTransport
