-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.attainer_credit_exceeds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:35.989873+00:00
-- url     : https://prove2.me/submissions/2c09c844-ab23-42eb-93b3-6b6152125e41

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

section

open ConsistentSubmodular
open ConsistentSubmodular.LowRollback
variable {m aCount : ℕ}

theorem solution (k q d₀ d p δ P : ℝ)
    (hk : 40 / 23 < k) (hk3 : k < 3) (hq : 0 ≤ q)
    (hd : 1 / 6 ≤ d) (hd₀ : 0 ≤ d₀) (hδ : 0 ≤ δ) (hPp : p ≤ P)
    (hI : 0 ≤ parentFloor k d₀ d p)
    (hF : 0 ≤ childPersistence q d p δ P) : ceiling k d₀ < P := by
  have hk0 : 0 < k := by linarith
  have h3 : 0 < 3 - k := by linarith
  have hqterm := mul_nonneg hq (show 0 ≤ P - p + δ by linarith)
  have hP : 4 * (p + d) ≤ 3 * P := by unfold childPersistence at hF; nlinarith only [hF, hqterm]
  have hmul := mul_le_mul_of_nonneg_left hP h3.le
  have hIfour := mul_nonneg (show 0 ≤ (4 : ℝ) by norm_num) hI
  have hfloor : 12 * d + 8 * (4 - k) * d₀ ≤ 3 * (3 - k) * P := by
    unfold parentFloor at hIfour
    nlinarith only [hmul, hIfour]
  have hkfloor := mul_le_mul_of_nonneg_left hfloor hk0.le
  have hkd := mul_le_mul_of_nonneg_left hd hk0.le
  have hC : k * ceiling k d₀ = 2 * k - 3 + 3 * (4 - k) * d₀ := by
    unfold ceiling
    field_simp
  have hCmul := congrArg (fun z : ℝ => 3 * (3 - k) * z) hC
  have hcoef : 0 ≤ (4 - k) * (17 * k - 27) * d₀ := by
    apply mul_nonneg _ hd₀
    apply mul_nonneg <;> linarith
  have hquad : 0 < 6 * k ^ 2 - 25 * k + 27 := by nlinarith [sq_nonneg (k - 25 / 12)]
  have hpos : 0 < 3 * k * (3 - k) * (P - ceiling k d₀) := by
    nlinarith only [hkfloor, hkd, hCmul, hcoef, hquad]
  have hden : 0 < 3 * k * (3 - k) := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hden).mp hpos)

end
