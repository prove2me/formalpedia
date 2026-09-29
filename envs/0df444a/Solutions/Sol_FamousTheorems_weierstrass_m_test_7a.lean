-- Prove2me | solution 1 for FamousTheorems.weierstrass_m_test_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:31:15.626663+00:00
-- url     : https://prove2.me/submissions/bc620593-64b5-4263-ae03-e8c321184e1b

import Mathlib

theorem solution {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ} {f : α → β → F}
    (hu : Summable u) (hfu : ∀ n x, ‖f n x‖ ≤ u n) :
    TendstoUniformly (fun (t : Finset α) (x : β) => ∑ n ∈ t, f n x) (fun x => ∑' n, f n x) Filter.atTop :=
  tendstoUniformly_tsum hu hfu
