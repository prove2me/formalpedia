-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.threshold_profile_eligible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:15.119493+00:00
-- url     : https://prove2.me/submissions/eca7cf3d-1cf4-4bc9-a42f-89f2b924c518

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access
import Theorems.Thm_ConsistentSubmodular_threshold_attainer_eligible

section

noncomputable section

namespace ConsistentSubmodular

variable {m atomCount : ℕ}

namespace AtomicProfile

variable (P : AtomicProfile m atomCount)

theorem attaining_equation (h s : Fin (m + 1)) (q : ℝ)
    (hd : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q) :
    (3 - q) * (P.designated s - P.residual h s) =
      q * (P.designated h - P.designated s) +
      ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s)) +
      3 * (1 - P.designated h) := by
  have hh := (div_eq_iff (ne_of_gt hd)).mp heq
  unfold rawNumerator at hh
  nlinarith only [hh]

end AtomicProfile

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s)
    (hA : (1281 : ℝ) / 1600 ≤ P.designated h) (hc : P.StrongCredit h)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hd : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q) :
    0 < P.actualEligibility h q s := by
  have hb := P.persistence_credit h s hhs
  have hatt := P.attaining_equation h s q hd heq
  have hh := threshold_attainer_eligible q (P.benchmark h - 1)
    (1 - P.designated h) (P.designated h - P.designated s)
    (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s))
    hq hq1 (by linarith [P.designated_le_one hP h]) (by linarith)
    (by linarith [P.one_le_benchmark hP h]) hc
    (sub_nonneg.mpr (P.designated_antitone hP hhs))
    (by unfold benchmark at *; linarith) hatt
  unfold actualEligibility
  nlinarith only [hh]

end
