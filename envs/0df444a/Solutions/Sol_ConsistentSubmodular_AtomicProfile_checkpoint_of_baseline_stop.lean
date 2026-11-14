-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.checkpoint_of_baseline_stop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:41.174944+00:00
-- url     : https://prove2.me/submissions/bcfea9a1-e46f-459e-93e1-6b6bacaa9cc8

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_rawEnvelope_attained
import Theorems.Thm_ConsistentSubmodular_baseline_stop_scalar
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_actual_test

section

namespace ConsistentSubmodular

variable (H P c α β L G R y A δ w q d d₀ kpar u z T Pt g a η n b : ℝ)

theorem eligibility_gap_identity :
    (4 * A - 3 - q * δ - (q - q ^ 2 / 4) * (A - δ - w)) -
      (w - (q - 1) * δ - 3 * (1 - A)) =
      (1 - (q - q ^ 2 / 4)) * (A - δ - w) := by
  ring

end ConsistentSubmodular

end

section

namespace ConsistentSubmodular

theorem actual_eligibility_of_suff (A q δ w : ℝ)
    (hr : 0 ≤ A - δ - w)
    (hsuff : 0 ≤ w - (q - 1) * δ - 3 * (1 - A)) :
    0 ≤ 4 * A - 3 - q * δ - (q - q ^ 2 / 4) * (A - δ - w) := by
  have hc : 0 ≤ 1 - (q - q ^ 2 / 4) := by
    nlinarith [sq_nonneg (q - 2)]
  have := mul_nonneg hc hr
  have hid := eligibility_gap_identity A δ w q
  linarith

end ConsistentSubmodular

end

section

namespace ConsistentSubmodular

noncomputable section

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem suff_implies_actual (h c : Fin (m + 1)) (q : ℝ)
    (hs : 0 ≤ P.suffEligibility h q c) : 0 ≤ P.actualEligibility h q c := by
  have hr := P.residual_nonnegative h c
  have ht := actual_eligibility_of_suff (P.designated h) q
    (P.designated h - P.designated c) (P.designated c - P.residual h c)
    (by linarith) hs
  unfold actualEligibility
  nlinarith only [ht]

end AtomicProfile

end

end ConsistentSubmodular

end

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

theorem solution (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 < P.designated h)
    (access : AccessCertificate P h)
    (hL : 3 * (1 - P.designated h) ≤ P.baseline h)
    (hq1 : 1 ≤ P.rawEnvelope h) (hq3 : P.rawEnvelope h ≤ 3 / 2) :
    Nonempty (CheckpointCertificate P) := by
  classical
  let q := P.rawEnvelope h
  have hqpos : 0 < q := by dsimp [q]; linarith
  obtain ⟨s, hs, hd, heq⟩ := P.rawEnvelope_attained h hqpos
  have hhs : h < s := (Finset.mem_filter.mp hs).2.1
  have hb := P.persistence_credit h s hhs.le
  have hatt := P.attaining_equation h s q hd heq
  have hscalar := baseline_stop_scalar (P.designated h) (3 * (1 - P.designated h))
    (P.designated h - P.designated s) (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s)) q
    (by linarith [P.designated_le_one hP h]) (by linarith)
    (sub_nonneg.mpr (P.designated_antitone hP hhs.le)) (by linarith) hq1 hq3 hatt
  have helig : 0 ≤ P.actualEligibility h q s :=
    P.suff_implies_actual h s q hscalar.1
  have henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t := by
    intro t ht ha
    exact P.rawEnvelope_valid hP h t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, ha⟩)
  rcases P.actual_test hP h access q hq1 (by dsimp [q]; linarith) henv with hyes | hno
  · exact hyes
  · have hf := hno s hhs (Finset.mem_filter.mp hs).2.2 helig
    have hc := hscalar.2
    nlinarith only [hf, hc]

end
