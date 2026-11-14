-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.root_attainer_suff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:31.623825+00:00
-- url     : https://prove2.me/submissions/67b0744d-1e30-46d2-b1fc-0b8b1a4a9bc4

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (hP : P.Canonical) (s : Fin (m + 1)) (q : ℝ)
    (hs : P.designated s < 1)
    (hd : 0 < P.designated 0 - P.residual 0 s) (heq : P.rawRatio 0 s = q) :
    0 < P.suffEligibility 0 q s := by
  have hδ : 0 < 1 - P.designated s := by linarith
  have hv := P.baseline_add_residual_monotone 0 (Fin.zero_le s)
  change P.baseline 0 + P.designated 0 ≤ P.baseline s + P.residual 0 s at hv
  rw [P.baseline_zero, zero_add] at hv
  change P.designated 0 ≤ P.baseline s + P.residual 0 s at hv
  rw [hP.1] at hv
  have heq' := (div_eq_iff (ne_of_gt hd)).mp heq
  unfold rawNumerator at heq'
  rw [hP.1] at heq' hd
  have hw : 0 ≤ P.designated s - P.residual 0 s := sub_nonneg.mpr (hP.2 s 0)
  have hsq := sq_pos_of_pos hδ
  have hid : (1 - P.residual 0 s) *
      ((P.designated s - P.residual 0 s) - (q - 1) * (1 - P.designated s)) =
      (1 - P.designated s) ^ 2 -
      (1 - P.designated s) * (P.designated s - P.residual 0 s) +
      (P.designated s - P.residual 0 s) ^ 2 +
      (1 - P.designated s) * ((P.benchmark s - 1) - (P.designated s - P.residual 0 s)) := by
    have hh := congrArg (fun x : ℝ => (1 - P.designated s) * x) heq'
    nlinarith only [hh]
  have hprod := mul_nonneg hδ.le
    (show 0 ≤ (P.benchmark s - 1) - (P.designated s - P.residual 0 s) by
      unfold benchmark
      linarith)
  unfold suffEligibility
  rw [hP.1]
  nlinarith [sq_nonneg ((P.designated s - P.residual 0 s) - (1 - P.designated s) / 2)]

end
