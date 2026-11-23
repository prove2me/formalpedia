-- Prove2me | solution 1 for DetANN.RelocCall.sim_inputState
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:54:53.041833+00:00
-- url     : https://prove2.me/submissions/23fbf580-a38b-4e4f-9ad3-bacfedafbe54

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_RelocCall

open PNormReg PNormRegLib DetANN in
/-- Start a relocated program on the standard preprocessing input layout from explicit host
register, base, window-memory, counter, running and program-counter equations. -/
theorem solution (p : RelocParams) (nR nQ : ℕ) (b R : ℤ) (c : ℕ) (r : State)
    {N m : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (θ : ℝ)
    (hreg : ∀ i < nR, r.core.regs (p.roff + i) = 0)
    (hptr : ∀ q < nQ, r.core.ptrs (p.qoff + q) = 0)
    (hbase : r.core.ptrs p.base = b)
    (hmem : ∀ z, |z| ≤ R → r.core.mem (b + z) = (inputState Y θ).core.mem z)
    (hint : ∀ z, |z| ≤ R → r.integerMemory (b + z) = (inputState Y θ).integerMemory z)
    (hcursor : r.cursor = 0) (hwork : r.work = c)
    (hr : r.halted = false) (hpc : r.core.pc = p.cOff) :
    Sim p (Frame.atHost nR nQ b R c r) r (inputState Y θ) := by
  apply Frame.sim_atHost p nR nQ b R c r (inputState Y θ)
  · simpa [inputState, PNormReg.initState] using hreg
  · simpa [inputState, PNormReg.initState] using hptr
  · exact hbase
  · exact hmem
  · exact hint
  · simpa [inputState, PNormReg.initState] using hcursor
  · simp [inputState, PNormReg.initState, hwork]
  · exact hr
  · simp [inputState, PNormReg.initState]
  · simp [inputState, PNormReg.initState, hpc]
