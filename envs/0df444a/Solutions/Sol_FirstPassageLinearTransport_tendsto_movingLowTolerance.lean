-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_movingLowTolerance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:43.622574+00:00
-- url     : https://prove2.me/submissions/848bdf2a-ffc2-402c-88e9-32a02e3b3b1b

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
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


section
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
private theorem tendsto_const_div_natCast_zero (K : ℝ) :
    Tendsto (fun L : ℕ => K / (L : ℝ)) atTop (nhds 0) := by
  have hcast : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun L : ℕ => ((L : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul hinv :
      Tendsto (fun L : ℕ => K * ((L : ℝ))⁻¹) atTop (nhds (K * 0)))
end
end FirstPassageLinearTransport
end

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (K₀ : ℝ) :
    Tendsto (movingLowTolerance K₀) atTop (nhds driftGap) := by
  change Tendsto (fun L : ℕ => driftGap - K₀ / (L : ℝ))
    atTop (nhds driftGap)
  simpa [movingLowTolerance] using
    (tendsto_const_nhds.sub (tendsto_const_div_natCast_zero K₀) :
      Tendsto (fun L : ℕ => driftGap - K₀ / (L : ℝ))
        atTop (nhds (driftGap - 0)))
end FirstPassageLinearTransport
