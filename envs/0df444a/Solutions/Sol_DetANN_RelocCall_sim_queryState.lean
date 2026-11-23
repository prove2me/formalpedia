-- Prove2me | solution 1 for DetANN.RelocCall.sim_queryState
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:57:59.292101+00:00
-- url     : https://prove2.me/submissions/8c4957e7-33f7-4b88-9a8b-8874243e9e70

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_RelocCall

open PNormReg PNormRegLib DetANN in
/-- Start a relocated query program on the standard query layout over a stored state `s`. -/
theorem solution (p : RelocParams) (nR nQ : ℕ) (b R : ℤ) (c : ℕ) (r s : State)
    (m : ℕ) (q : EuclideanSpace ℝ (Fin m))
    (hreg : ∀ i < nR, r.core.regs (p.roff + i) = 0)
    (hptr : ∀ u < nQ, r.core.ptrs (p.qoff + u) = 0)
    (hbase : r.core.ptrs p.base = b)
    (hmem : ∀ z, |z| ≤ R → r.core.mem (b + z) = (queryState m s q).core.mem z)
    (hint : ∀ z, |z| ≤ R → r.integerMemory (b + z) = (queryState m s q).integerMemory z)
    (hcursor : r.cursor = 0) (hwork : r.work = c)
    (hr : r.halted = false) (hpc : r.core.pc = p.cOff) :
    Sim p (Frame.atHost nR nQ b R c r) r (queryState m s q) := by
  apply Frame.sim_atHost p nR nQ b R c r (queryState m s q)
  · simpa [queryState] using hreg
  · simpa [queryState] using hptr
  · exact hbase
  · exact hmem
  · exact hint
  · simpa [queryState] using hcursor
  · simp [queryState, hwork]
  · exact hr
  · simp [queryState]
  · simp [queryState, hpc]
