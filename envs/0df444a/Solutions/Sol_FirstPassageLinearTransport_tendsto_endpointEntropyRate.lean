-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_endpointEntropyRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:36.233169+00:00
-- url     : https://prove2.me/submissions/3aef254c-69d0-4577-84f4-51e8f898a680

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Theorems.Thm_FirstPassageLinearTransport_continuous_binaryBarrierRate
import Theorems.Thm_FirstPassageLinearTransport_tendsto_endpointLambda
import Theorems.Thm_FirstPassageLinearTransport_tendsto_endpointTolerance
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
theorem _root_.solution :
    Tendsto
      (fun n : ℕ =>
        adjustableEntropyRate (endpointLambda n) (endpointTolerance n))
      atTop (nhds firstPassageEndpointRate) := by
  have hdisp : Tendsto
      (fun n : ℕ => adjustableBarrierDisplacement
        (endpointLambda n) (endpointTolerance n))
      atTop (nhds firstPassageEndpointDisplacement) := by
    have hmul := tendsto_endpointLambda.mul tendsto_endpointTolerance
    simpa [adjustableBarrierDisplacement, firstPassageEndpointDisplacement]
      using hmul.div_const logTwoThree
  unfold adjustableEntropyRate firstPassageEndpointRate
  exact continuous_binaryBarrierRate.continuousAt.tendsto.comp hdisp
end FirstPassageLinearTransport
