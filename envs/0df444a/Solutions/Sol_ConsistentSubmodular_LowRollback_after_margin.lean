-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.after_margin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:33.372207+00:00
-- url     : https://prove2.me/submissions/89c56c51-2781-48d4-ae4d-3d661d6eae24

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets

section

open ConsistentSubmodular
open ConsistentSubmodular.LowRollback
variable {m aCount : ℕ}

theorem solution (k d₀ d p δ P T Pt z u zs : ℝ)
    (hk : 3 / 2 < k) (hk3 : k < 3)
    (hs : zs ≤ (k - 1) * (d + δ) + (4 - k) * d₀)
    (ht : z ≤ (k - 1) * T + (4 - k) * d₀)
    (hchild : 0 ≤ Pt - p - u) (hres : 0 ≤ 1 - T - u)
    (hparent : 0 ≤ Pt - P - z + zs) :
    Y k d₀ d p δ P ≤ M₂ k T Pt z u := by
  have hk0 : 0 < k := by linarith
  have hL : 0 ≤ (k - 1) * (3 - k) := mul_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ k ^ 2 - 3 * k + 3 := by nlinarith [sq_nonneg (k - 3 / 2)]
  have h1 := mul_nonneg (show 0 ≤ (3 : ℝ) by norm_num) (sub_nonneg.mpr ht)
  have h2 := mul_nonneg hB hchild
  have h3 := mul_nonneg (show 0 ≤ 2 * k - 3 by linarith) hres
  have h4 := mul_nonneg hL hparent
  have h5 := mul_nonneg hL (sub_nonneg.mpr hs)
  have heq : k * (M₂ k T Pt z u - Y k d₀ d p δ P) =
      3 * ((k - 1) * T + (4 - k) * d₀ - z) + (k ^ 2 - 3 * k + 3) * (Pt - p - u)+
      (2 * k - 3) * (1 - T - u) + (k - 1) * (3 - k) * (Pt - P - z + zs)+
      (k - 1) * (3 - k) * ((k - 1) * (d + δ) + (4 - k) * d₀ - zs) := by
    unfold M₂ Y ceiling
    field_simp
    ring
  have hm : 0 ≤ k * (M₂ k T Pt z u - Y k d₀ d p δ P) := by rw [heq]; linarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hk0).mp hm)

end
