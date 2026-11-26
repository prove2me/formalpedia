-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_movingLowCorrectionGap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:12.736909+00:00
-- url     : https://prove2.me/submissions/121bcbdf-9ced-4e27-a147-289c52dcf431

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowTolerance
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowLambda
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
theorem _root_.solution (K₀ K₁ : ℝ) :
    Tendsto
      (fun L : ℕ =>
        a0 + movingLowTolerance K₀ L -
          2 * movingLowLambda K₁ L * movingLowTolerance K₀ L)
      atTop (nhds (2 * a0 - 1)) := by
  have htol := tendsto_movingLowTolerance K₀
  have hlam := tendsto_movingLowLambda K₁
  have hprod := hlam.mul htol
  have ha0 : Tendsto (fun _ : ℕ => a0) atTop (nhds a0) :=
    tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hlim := (ha0.add htol).sub (htwo.mul hprod)
  have hlimitEq :
      a0 + driftGap - 2 * (1 * driftGap) = 2 * a0 - 1 := by
    unfold driftGap
    ring
  rw [hlimitEq] at hlim
  simpa [mul_assoc] using hlim
end FirstPassageLinearTransport
