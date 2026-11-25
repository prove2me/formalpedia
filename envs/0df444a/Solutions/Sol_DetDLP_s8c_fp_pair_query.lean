-- Prove2me | solution 1 for DetDLP.s8c_fp_pair_query
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:25:39.963729+00:00
-- url     : https://prove2.me/submissions/8c0fba64-fceb-4fe7-8665-ba7b0e558ac0

import Theorems.Thm_DetDLP_s8c_fp_elem_and_pair_queries

set_option autoImplicit false

/-- The pair-query case is the restriction of the published element-and-pair query theorem. -/
theorem solution : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [5] := by
  intro h
  obtain ⟨make, port, L, hm, hp, hall⟩ := DetDLP.s8c_fp_elem_and_pair_queries h
  refine ⟨make, port, L, hm, hp, ?_⟩
  intro t ht base payload b n hq
  have ht' : t ∈ ([3, 5] : List ℕ) := by simp [ht]
  exact hall t ht' base payload b n hq
