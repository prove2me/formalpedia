-- Prove2me | solution 1 for FredholmBanach.compact_perturbation_ker_range
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:48:44.730317+00:00
-- url     : https://prove2.me/submissions/2b09831a-d891-43b1-a56a-fd57c443e984

import Theorems.Thm_FredholmBanach_finiteDimensional_ker_isClosed_range_iff

open Topology Filter

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {u h : E →L[𝕜] F} (hk : FiniteDimensional 𝕜 u.ker) (hr : IsClosed (u.range : Set F))
    (hh : IsCompactOperator h) :
    FiniteDimensional 𝕜 (u + h).ker ∧ IsClosed ((u + h).range : Set F) := by
  have hS := (FredholmBanach.finiteDimensional_ker_isClosed_range_iff u).1 ⟨hk, hr⟩
  refine (FredholmBanach.finiteDimensional_ker_isClosed_range_iff (u + h)).2 ?_
  rintro x ⟨C, hC⟩ y hy
  have hx : ∀ n, x n ∈ Metric.closedBall (0 : E) C := fun n => mem_closedBall_zero_iff.2 (hC n)
  have hcpt : IsCompact (closure (h '' Metric.closedBall (0 : E) C)) :=
    hh.isCompact_closure_image_closedBall C
  obtain ⟨z, -, ψ, hψ, hz⟩ := hcpt.tendsto_subseq (fun n => subset_closure ⟨x n, hx n, rfl⟩)
  have hu : Tendsto (fun n => u ((x ∘ ψ) n)) atTop (𝓝 (y - z)) := by
    refine ((hy.comp hψ.tendsto_atTop).sub hz).congr fun n => ?_
    simp
  obtain ⟨a, φ, hφ, ha⟩ := hS (x ∘ ψ) ⟨C, fun n => hC _⟩ (y - z) hu
  exact ⟨a, ψ ∘ φ, hψ.comp hφ, ha⟩
