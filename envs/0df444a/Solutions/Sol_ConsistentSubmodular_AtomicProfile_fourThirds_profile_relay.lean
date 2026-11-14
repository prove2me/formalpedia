-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.fourThirds_profile_relay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:16.717506+00:00
-- url     : https://prove2.me/submissions/4c86624d-e6f8-4386-80f1-c49e968cd29a

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access
import Theorems.Thm_ConsistentSubmodular_fourThirds_strict_relay

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

namespace ConsistentSubmodular

noncomputable section

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem strict_edge_child (hP : P.Canonical) (h s : Fin (m + 1)) (hhs : h ≤ s)
    (hstrict : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (3 : ℝ) / 4 < P.designated h -
      (P.designated h - P.designated s) * z - P.residual h s * z * (1 - z)) :
    (3 : ℝ) / 4 < P.designated s ∧ P.StrongCredit s := by
  refine ⟨?_, P.strongCredit_of_pessimisticEdge hP h s hhs (fun z hz hz1 => (hstrict z hz hz1).le)⟩
  have := hstrict 1 (by norm_num) (by norm_num)
  norm_num at this
  linarith

end AtomicProfile

end

end ConsistentSubmodular

end

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h < s)
    (hA : (3 : ℝ) / 4 < P.designated h) (hcredit : P.StrongCredit h)
    (q : ℝ) (hq : (4 : ℝ) / 3 ≤ q) (hq2 : q ≤ 2)
    (hden : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q)
    (hfail : q * (P.benchmark s - P.designated h) <
      2 * P.designated h * q - 3 * (4 * P.designated h - 3)) :
    P.PessimisticSafeEdge h s ∧ (3 : ℝ) / 4 < P.designated s ∧ P.StrongCredit s := by
  have hA1 := P.designated_le_one hP h
  have hδ := sub_nonneg.mpr (P.designated_antitone hP hhs.le)
  have hw := sub_nonneg.mpr (hP.2 s h)
  have hr := P.residual_nonnegative h s
  have hp := P.one_le_benchmark hP h
  have hper := P.persistence_credit h s hhs.le
  have hatt := P.attaining_equation h s q hden heq
  have hscalar := fourThirds_strict_relay (1 - P.designated h)
    (P.benchmark h - 1) (P.designated h - P.designated s)
    (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s)) q
    (by linarith) (by linarith) (by linarith) hcredit hδ hw (by linarith)
    (by linarith) (by unfold benchmark at *; linarith) hq hq2
    (by nlinarith only [hatt]) (by nlinarith only [hfail])
  have hstrict : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (3 : ℝ) / 4 < P.designated h -
      (P.designated h - P.designated s) * z - P.residual h s * z * (1 - z) := by
    intro z hz hz1
    have := hscalar z hz hz1
    nlinarith only [this]
  exact ⟨fun z hz hz1 => (hstrict z hz hz1).le, P.strict_edge_child hP h s hhs.le hstrict⟩

end
