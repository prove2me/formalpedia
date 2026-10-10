-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.defect_orbit_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:16:20.163977+00:00
-- url     : https://prove2.me/submissions/ed5cf67a-8800-48aa-9dc3-9048bd116d41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.defect_orbit_le
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Theorems.Thm_BookProof_BrstUnboundedLeakage_truncGen_isSelfAdjoint
import Theorems.Thm_BookProof_BrstUnboundedLeakage_flow_truncGen_mem
import Theorems.Thm_BookProof_BrstUnboundedLeakage_flow_truncGen_mem_domain
import Theorems.Thm_BookProof_BrstUnboundedLeakage_defect_eq_truncDefect
import Theorems.Thm_BookProof_BrstLeakage_norm_flow_apply
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

set_option maxHeartbeats 1000000 in
theorem solution {x : H} (hx : x ∈ V) (s : ℝ) :
    ‖T.op ⟨flow (truncGen T V hV) s x, flow_truncGen_mem_domain T V hV s hx⟩
        - truncGen T V hV (flow (truncGen T V hV) s x)‖ ≤ ‖truncDefect T V hV‖ * ‖x‖ := by

  have hsa : IsSelfAdjoint (truncGen T V hV) := truncGen_isSelfAdjoint T V hV
  have hmem : flow (truncGen T V hV) s x ∈ V := flow_truncGen_mem T V hV s hx
  rw [defect_eq_truncDefect T V hV hmem]
  calc ‖truncDefect T V hV (flow (truncGen T V hV) s x)‖
      ≤ ‖truncDefect T V hV‖ * ‖flow (truncGen T V hV) s x‖ := (truncDefect T V hV).le_opNorm _
    _ = ‖truncDefect T V hV‖ * ‖x‖ := by rw [norm_flow_apply hsa]
