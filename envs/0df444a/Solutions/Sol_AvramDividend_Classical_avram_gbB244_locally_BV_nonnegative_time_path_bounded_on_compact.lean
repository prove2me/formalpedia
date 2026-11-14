-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB244_locally_BV_nonnegative_time_path_bounded_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:25.299323+00:00
-- url     : https://prove2.me/submissions/287fb11c-9c07-4f82-871a-1645ffdc6ec1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Jordan components bound a locally BV path on each compact nonnegative time interval. -/
theorem solution
    (f : ℝ≥0 → ℝ)
    (hFV : LocallyBoundedVariationOn f Set.univ)
    (T : ℝ≥0) :
    ∃ lo hi : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
      lo ≤ f t ∧ f t ≤ hi := by
  obtain ⟨p, q, hp, hq, hf⟩ :=
    hFV.exists_monotoneOn_sub_monotoneOn
  refine ⟨p 0 - q T, p T - q 0, ?_⟩
  intro t ht
  have hp0 : p 0 ≤ p t :=
    hp (Set.mem_univ _) (Set.mem_univ _) ht.1
  have hpT : p t ≤ p T :=
    hp (Set.mem_univ _) (Set.mem_univ _) ht.2
  have hq0 : q 0 ≤ q t :=
    hq (Set.mem_univ _) (Set.mem_univ _) ht.1
  have hqT : q t ≤ q T :=
    hq (Set.mem_univ _) (Set.mem_univ _) ht.2
  have hft : f t = p t - q t := by
    rw [hf]
    rfl
  constructor <;> linarith
