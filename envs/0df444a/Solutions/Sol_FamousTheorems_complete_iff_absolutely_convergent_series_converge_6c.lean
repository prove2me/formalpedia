-- Prove2me | solution 1 for FamousTheorems.complete_iff_absolutely_convergent_series_converge_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:49:41.634053+00:00
-- url     : https://prove2.me/submissions/d8b1eba4-de8d-4a38-a5fd-a11776c3670b

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] :
    (∀ u : ℕ → E, Summable (fun n => ‖u n‖) →
      ∃ a, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, u i) Filter.atTop (nhds a)) ↔
    CompleteSpace E :=
  NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace
