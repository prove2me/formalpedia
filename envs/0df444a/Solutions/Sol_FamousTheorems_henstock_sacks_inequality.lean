-- Prove2me | solution 1 for FamousTheorems.henstock_sacks_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:35:21.441111+00:00
-- url     : https://prove2.me/submissions/b87e829c-77f7-401d-b417-44ea5ce2a45a

import Mathlib

theorem solution {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {I : BoxIntegral.Box ι} {l : BoxIntegral.IntegrationParams} {f : (ι → ℝ) → E}
    {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} (h : BoxIntegral.Integrable I l f vol) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : NNReal → (ι → ℝ) → Set.Ioi (0 : ℝ),
      (∀ (c : NNReal) (π : BoxIntegral.TaggedPrepartition I), l.MemBaseSet I c (r c) π → π.IsPartition →
        dist (BoxIntegral.integralSum f vol π) (BoxIntegral.integral I l f vol) ≤ ε) ∧
      ∀ (c : NNReal) (π : BoxIntegral.TaggedPrepartition I) (π₀ : BoxIntegral.Prepartition I),
        l.MemBaseSet I c (r c) π → π.iUnion = π₀.iUnion →
          dist (BoxIntegral.integralSum f vol π) (∑ J ∈ π₀.boxes, BoxIntegral.integral J l f vol) ≤ ε :=
  ⟨h.convergenceR ε, fun _ _ hπ hp => h.dist_integralSum_integral_le_of_memBaseSet hε hπ hp,
    fun _ _ _ hπ hU => h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq hε hπ hU⟩
