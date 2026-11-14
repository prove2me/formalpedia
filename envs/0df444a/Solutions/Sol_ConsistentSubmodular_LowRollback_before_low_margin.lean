-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.before_low_margin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:32.784958+00:00
-- url     : https://prove2.me/submissions/049395d7-a75e-4768-8abc-7836cc96691e

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets

section

open ConsistentSubmodular
open ConsistentSubmodular.LowRollback
variable {m aCount : ℕ}

theorem solution (k d₀ d p δ Δ Pt z u : ℝ)
    (hk : 3 / 2 ≤ k) (hk2 : k ≤ 2) (hΔ : Δ ≤ δ)
    (hp : 0 ≤ Pt - p - u) (hcap : z ≤ (k - 1) * (d + Δ) + (4 - k) * d₀) :
    V k d₀ d p δ ≤ max (M₁ k (d + Δ) Pt z u) (M₂ k (d + Δ) Pt z u) := by
  have hbase : V k d₀ d p δ ≤ d + Δ + p - 2 * z := by
    have hc := mul_nonneg (show 0 ≤ 2 * k - 3 by linarith) (sub_nonneg.mpr hΔ)
    unfold V
    nlinarith
  by_cases hzu : u ≤ z
  · apply hbase.trans
    apply le_trans _ (le_max_left _ _)
    have hm := mul_nonneg (show 0 ≤ k - 1 by linarith) (sub_nonneg.mpr hzu)
    unfold M₁
    nlinarith
  · apply hbase.trans
    apply le_trans _ (le_max_right _ _)
    have hm := mul_nonneg (sub_nonneg.mpr hk2) (sub_nonneg.mpr (le_of_not_ge hzu))
    unfold M₂
    nlinarith

end
