-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.headline_oracle_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T05:48:02.573632+00:00
-- url     : https://prove2.me/submissions/ca48540f-db89-4715-8aaa-467a3866b287
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ChenCapacityTerminals_Exact_RootedHeadline
import Definitions.Def_ChenCapacityTerminals_Exact_FlowCompilation
import Theorems.Thm_ChenCapacityTerminals_Exact_terminals_rooted_expansion
import Theorems.Thm_ChenCapacityTerminals_Exact_pinning_conditioning
import Theorems.Thm_ChenCapacityTerminals_Exact_conditioned_batching
import Theorems.Thm_ChenCapacityTerminals_Exact_schedule_and_packing_realization
import Theorems.Thm_ChenCapacityTerminals_Exact_global_reversal_realization
import Theorems.Thm_ChenCapacityTerminals_Exact_deterministic_integer_flow

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution :
    ∃ P : ChenCapacityTerminals.Exact.WordProgram,
      ChenCapacityTerminals.Exact.HeadlineReduction P := by
  classical
  obtain ⟨S, hSF⟩ := deterministic_integer_flow
  obtain ⟨B, k, hB, hS⟩ := hSF 1 1
  obtain ⟨C, hC, hS⟩ := hS 1 (by norm_num)
  have hall : ∀ Q : IntegerQuery, Q.Valid → ∃ A : IntegerAnswer, A.Correct Q := by
    intro Q hQ
    let scale : ℕ := 2 + Q.graph.n + Q.graph.arcs.length +
      (Q.graph.arcs.map IntegerArc.capacity).sum
    have hscale : 2 ≤ scale := by dsimp [scale]; omega
    have hsize : Q.graph.n + Q.graph.arcs.length ≤ scale ^ 1 := by
      simp only [pow_one]
      dsimp [scale]
      omega
    have hcap : ∀ e ∈ Q.graph.arcs, e.capacity ≤ scale ^ 1 := by
      intro e he
      simp only [pow_one]
      have hle : e.capacity ≤ (Q.graph.arcs.map IntegerArc.capacity).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem he)
      dsimp [scale]
      omega
    obtain ⟨time, htime, ticks, m, hexec, hout, rfl⟩ :=
      hS Q scale ⟨hQ, hscale, hsize, hcap⟩
        (B * (Nat.log2 scale + 1)) (le_refl _)
    exact ⟨hout.choose, hout.choose_spec.1⟩
  have horacle : ∃ O, LawfulWordOracle O := by
    let O : IntegerQuery → IntegerAnswer := fun Q =>
      if h : ∃ A : IntegerAnswer, A.Correct Q then h.choose else ⟨[], ∅⟩
    refine ⟨O, ?_⟩
    intro Q hQ
    have h := hall Q hQ
    simp only [O, dif_pos h]
    exact h.choose_spec
  obtain ⟨P, hP⟩ := schedule_and_packing_realization
    terminals_rooted_expansion pinning_conditioning conditioned_batching horacle
  exact global_reversal_realization P hP
