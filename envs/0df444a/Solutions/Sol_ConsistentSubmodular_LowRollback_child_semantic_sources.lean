-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.child_semantic_sources
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:35.381961+00:00
-- url     : https://prove2.me/submissions/e67a17cf-56b7-41d7-8f67-5b8f37e5c2c2

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

section

noncomputable section

namespace ConsistentSubmodular

namespace LowRollback

variable {m aCount : ℕ}

theorem gap_le_designated (P : AtomicProfile m aCount) (i t : Fin (m + 1)) :
    gap P i t ≤ P.designated t := sub_le_self _ (P.residual_nonnegative i t)

/-- Parent history remains available from every earlier row, not only from the
current carrier. This is the essential after-attainer source. -/
theorem cross_row_persistence (P : AtomicProfile m aCount) (i s t : Fin (m + 1))
    (hst : s ≤ t) : 0 ≤ shifted P t - shifted P s - gap P i t + gap P i s := by
  have hp := P.baseline_add_residual_monotone i hst
  unfold shifted gap AtomicProfile.benchmark
  linarith

theorem carrier_persistence (P : AtomicProfile m aCount) (h t : Fin (m + 1)) (hht : h ≤ t) :
    0 ≤ shifted P t - shifted P h - gap P h t := by
  have hp := cross_row_persistence P h h t hht
  rw [gap_self] at hp
  linarith

end LowRollback

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace LowRollback

variable {m aCount : ℕ}

theorem attainment_shifted (P : AtomicProfile m aCount) (a h : Fin (m + 1)) (k : ℝ)
    (hden : 0 < P.designated a - P.residual a h) (hatt : P.rawRatio a h = k) :
    shifted P h = (4 - k) * gap P a h - k * deficit P h - (4 - k) * deficit P a := by
  have heq := (div_eq_iff (ne_of_gt hden)).mp hatt
  unfold AtomicProfile.rawNumerator at heq
  unfold shifted deficit gap
  nlinarith only [heq]

theorem child_attainment (P : AtomicProfile m aCount) (h s : Fin (m + 1)) (q : ℝ)
    (hden : 0 < P.designated h - P.residual h s) (hatt : P.rawRatio h s = q) :
    shifted P s = (4 - q) * gap P h s - q * (deficit P s - deficit P h) - 4 * deficit P h := by
  have hp := attainment_shifted P h s q hden hatt
  nlinarith only [hp]

theorem child_actual_margin (P : AtomicProfile m aCount) (h s : Fin (m + 1)) (q : ℝ)
    (hden : 0 < P.designated h - P.residual h s) (hatt : P.rawRatio h s = q) :
    4 * P.actualEligibility h q s =
      q * shifted P s + (q - 2) ^ 2 - (4 - q) ^ 2 * deficit P h := by
  rw [child_attainment P h s q hden hatt]
  unfold AtomicProfile.actualEligibility deficit gap
  ring

end LowRollback

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.LowRollback
variable {m aCount : ℕ}

theorem solution (P : AtomicProfile m aCount) (_hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s) (q : ℝ) (hq4 : q ≤ 4)
    (hden : 0 < P.designated h - P.residual h s) (hatt : P.rawRatio h s = q)
    (hno : P.actualEligibility h q s ≤ 0) :
    0 ≤ childPersistence q (deficit P h) (shifted P h)
      (deficit P s - deficit P h) (shifted P s) ∧
    0 ≤ childCapacity q (deficit P h) (deficit P s - deficit P h) (shifted P s) ∧
    0 ≤ childIneligibility q (deficit P h) (shifted P s) := by
  have heq := child_attainment P h s q hden hatt
  have hp := carrier_persistence P h s hhs
  have hc := gap_le_designated P h s
  have hmulP := mul_nonneg (sub_nonneg.mpr hq4) hp
  have hmulC := mul_nonneg (sub_nonneg.mpr hq4) (sub_nonneg.mpr hc)
  have hE := child_actual_margin P h s q hden hatt
  unfold childPersistence childCapacity childIneligibility
  dsimp [deficit] at *
  constructor
  · nlinarith only [heq, hmulP]
  constructor
  · nlinarith only [heq, hmulC]
  · linarith

end
