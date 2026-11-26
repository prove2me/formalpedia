-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_natLogTwo_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:35.737324+00:00
-- url     : https://prove2.me/submissions/9e882a00-eca2-4867-bbb7-fbb8b70d456a

import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop := by
  rw [tendsto_atTop]
  intro L
  filter_upwards [eventually_ge_atTop (2 ^ L)] with N hN
  have hlog := Nat.log_mono_right (b := 2) hN
  simpa [Nat.log_pow (by norm_num : 1 < 2)] using hlog
end FirstPassageLinearTransport
