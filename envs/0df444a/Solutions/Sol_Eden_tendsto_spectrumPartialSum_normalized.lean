-- Prove2me | solution 1 for Eden.tendsto_spectrumPartialSum_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:24.781988+00:00
-- url     : https://prove2.me/submissions/fd279cd0-9441-4eb1-b768-945dd456cdd8

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
import Theorems.Thm_Eden_tendsto_lyapunovExponent


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) (k : ℕ) :
    Tendsto (fun t => spectrumPartialSum (normalizedLogSingularValues c t p) k)
      atTop (𝓝 (spectrumPartialSum (lyapunovExponent c p) k)) := by
  unfold spectrumPartialSum
  apply tendsto_finsetSum
  intro i hi
  unfold spectrumEntry
  split_ifs with h
  · exact tendsto_lyapunovExponent c p ⟨i, h⟩
  · exact tendsto_const_nhds
end Eden
