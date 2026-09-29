-- Prove2me | solution 1 for FamousTheorems.tannery_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:07:59.861417+00:00
-- url     : https://prove2.me/submissions/a998e9e7-ed23-419d-bb3e-d9ef677b2641

import Mathlib

theorem solution {α β G : Type*} {𝓕 : Filter α} [NormedAddCommGroup G] [CompleteSpace G] {f : α → β → G}
    {g : β → G} {bound : β → ℝ} (h_sum : Summable bound)
    (hab : ∀ k, Filter.Tendsto (fun x => f x k) 𝓕 (nhds (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Filter.Tendsto (fun x => ∑' k, f x k) 𝓕 (nhds (∑' k, g k)) :=
  tendsto_tsum_of_dominated_convergence h_sum hab h_bound
