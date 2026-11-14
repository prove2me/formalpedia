-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.source_parameter_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:37.248017+00:00
-- url     : https://prove2.me/submissions/38ae89ef-20aa-4e13-8d00-7b108d0ef619

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

section

set_option maxHeartbeats 1500000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem solution (k d₀ d p : ℝ)
    (hk0 : 4 / 3 ≤ k) (hk3 : k < 3) (hd : 319 / 1600 ≤ d) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ parentFloor k d₀ d p) (hp : p < ceiling k d₀) : k < 40 / 17 := by
  by_cases hk9 : k < 9 / 5
  · linarith
  have hk : 0 < k := by linarith
  have h3 : 0 < 3 - k := by linarith
  have hC : k * ceiling k d₀ = 2 * k - 3 + 3 * (4 - k) * d₀ := by unfold ceiling; field_simp
  have hI' := mul_nonneg hk.le hI
  have hp' := mul_lt_mul_of_pos_left hp (mul_pos hk h3)
  have heq := congrArg (fun z : ℝ => (3 - k) * z) hC
  have hpoly : (d + 2) * k ^ 2 - 9 * k + 9 < (4 - k) * (9 - 5 * k) * d₀ := by
    unfold parentFloor at hI'
    nlinarith only [hI', hp', heq]
  have hright : (4 - k) * (9 - 5 * k) * d₀ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) hd₀
  have hd' := mul_le_mul_of_nonneg_right hd (sq_nonneg k)
  have hfactor : 9 * (23 * k - 40) * (17 * k - 40) < 0 := by nlinarith only [hpoly, hright, hd']
  have hfirst : 0 < 9 * (23 * k - 40) := by linarith
  have hsecond : 17 * k - 40 < 0 := by nlinarith only [hfactor, hfirst]
  linarith

end
