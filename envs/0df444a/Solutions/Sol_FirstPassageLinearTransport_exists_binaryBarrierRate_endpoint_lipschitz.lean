-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_binaryBarrierRate_endpoint_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:09.269843+00:00
-- url     : https://prove2.me/submissions/ef9027ab-f42a-43cf-a042-209cf1c941a6

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointDisplacement_lt_half
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointDisplacement_pos
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
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
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ Set.Icc (firstPassageEndpointDisplacement / 2)
          firstPassageEndpointDisplacement,
        ∀ y ∈ Set.Icc (firstPassageEndpointDisplacement / 2)
          firstPassageEndpointDisplacement,
          ‖binaryBarrierRate y - binaryBarrierRate x‖ ≤ C * ‖y - x‖ := by
  let pLo := 1 / 2 + firstPassageEndpointDisplacement / 2
  let pHi := 1 / 2 + firstPassageEndpointDisplacement
  let derivWeight : ℝ → ℝ := fun p => ‖Real.log (1 - p) - Real.log p‖
  have hpLo0 : 0 < pLo := by
    dsimp [pLo]
    linarith [firstPassageEndpointDisplacement_pos]
  have hpHi1 : pHi < 1 := by
    dsimp [pHi]
    linarith [firstPassageEndpointDisplacement_lt_half]
  have hcont : ContinuousOn derivWeight (Set.Icc pLo pHi) := by
    intro p hp
    have hp0 : p ≠ 0 := by linarith [hp.1, hpLo0]
    have hp1 : 1 - p ≠ 0 := by linarith [hp.2, hpHi1]
    dsimp [derivWeight]
    have honeSub : ContinuousAt (fun z : ℝ => 1 - z) p :=
      continuousAt_const.sub continuousAt_id
    have hlogOne : ContinuousAt (fun z : ℝ => Real.log (1 - z)) p :=
      by simpa [Function.comp_def] using
        (Real.continuousAt_log hp1).comp honeSub
    have hlog : ContinuousAt (fun z : ℝ => Real.log z) p :=
      Real.continuousAt_log hp0
    exact (hlogOne.sub hlog).norm.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.bddAbove_image hcont
  let C := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  have hxp : 1 / 2 + x ∈ Set.Icc pLo pHi := by
    dsimp [pLo, pHi]
    constructor <;> linarith [hx.1, hx.2]
  have hyp : 1 / 2 + y ∈ Set.Icc pLo pHi := by
    dsimp [pLo, pHi]
    constructor <;> linarith [hy.1, hy.2]
  have hdiff : ∀ p ∈ Set.Icc pLo pHi,
      DifferentiableAt ℝ Real.binEntropy p := by
    intro p hp
    apply Real.differentiableAt_binEntropy
    · linarith [hp.1, hpLo0]
    · linarith [hp.2, hpHi1]
  have hbound : ∀ p ∈ Set.Icc pLo pHi,
      ‖deriv Real.binEntropy p‖ ≤ C := by
    intro p hp
    have himage : derivWeight p ∈
        derivWeight '' Set.Icc pLo pHi := ⟨p, hp, rfl⟩
    have hpBound : derivWeight p ≤ C₀ := hC₀ himage
    rw [Real.deriv_binEntropy]
    exact hpBound.trans (le_max_left _ _)
  have hmean := (convex_Icc pLo pHi).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound hxp hyp
  unfold binaryBarrierRate
  calc
    ‖(Real.log 2 - Real.binEntropy (1 / 2 + y)) -
        (Real.log 2 - Real.binEntropy (1 / 2 + x))‖ =
      ‖Real.binEntropy (1 / 2 + y) - Real.binEntropy (1 / 2 + x)‖ := by
        rw [show
          (Real.log 2 - Real.binEntropy (1 / 2 + y)) -
              (Real.log 2 - Real.binEntropy (1 / 2 + x)) =
            -(Real.binEntropy (1 / 2 + y) -
              Real.binEntropy (1 / 2 + x)) by ring,
          norm_neg]
    _ ≤ C * ‖(1 / 2 + y) - (1 / 2 + x)‖ := hmean
    _ = C * ‖y - x‖ := by congr 2 <;> ring
end FirstPassageLinearTransport
