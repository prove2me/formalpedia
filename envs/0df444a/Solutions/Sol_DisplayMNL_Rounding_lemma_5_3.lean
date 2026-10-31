-- Prove2me | solution 1 for DisplayMNL.Rounding.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:37:05.78299+00:00
-- url     : https://prove2.me/submissions/de6e8fe6-9b44-4a53-a674-155990de8541

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model
import Theorems.Thm_DisplayMNL_Rounding_lemma_5_3_subset

open Finset

open DisplayMNL.Rounding in
theorem solution {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j ≤ s.T) :
    wt I (pre A (etil s kmid j)) ≤ wt I (s.sp j) := by
  have hsub := lemma_5_3_subset I ε kmid s A hst hk1 hk2 hF hR j hj1 hjT
  unfold wt
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (hst.2.2.1 i).le)
