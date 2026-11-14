-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.selector_large_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:04.913201+00:00
-- url     : https://prove2.me/submissions/f757875a-9eab-4742-9c36-5dfca4423d13

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorRelays
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_rawEnvelope_attained
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_high_parameter_profile_relay
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_actual_test
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_suff_test
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_fourThirds_profile_relay

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

/-- Every attaining row is sufficient-eligible from four thirds onward, given
the baseline budget supplied by strong credit. -/
theorem attaining_suff_eligible (D δ w b q : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hb : 2 * D / 3 ≤ b)
    (hq : (4 : ℝ) / 3 ≤ q) (hq3 : q < 3)
    (hatt : (3 - q) * w = q * δ + b + D) :
    0 ≤ w - (q - 1) * δ - D := by
  have hcoef : 0 ≤ q ^ 2 - 3 * q + 3 := by
    nlinarith [sq_nonneg (q - 3 / 2)]
  have h1 := mul_nonneg hcoef hδ
  have h2 := mul_nonneg (show 0 ≤ q - 4 / 3 by linarith) hD
  have hid : (3 - q) * (w - (q - 1) * δ - D) =
      b - (2 - q) * D + (q ^ 2 - 3 * q + 3) * δ := by
    nlinarith only [hatt]
  nlinarith

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

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem attainer_suff_of_fourThirds (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s)
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hc : P.StrongCredit h)
    (q : ℝ) (hq : (4 : ℝ) / 3 ≤ q) (hq3 : q < 3)
    (hd : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q) :
    0 ≤ P.suffEligibility h q s := by
  have hl := P.strongCredit_baseline hP h hA hc
  have hb := P.persistence_credit h s hhs
  have hatt := P.attaining_equation h s q hd heq
  have hh := attaining_suff_eligible (3 * (1 - P.designated h))
    (P.designated h - P.designated s) (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s)) q
    (by linarith [P.designated_le_one hP h])
    (sub_nonneg.mpr (P.designated_antitone hP hhs)) (by linarith) hq hq3 hatt
  exact hh

end AtomicProfile

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (hP : P.Canonical) (h : Fin (m + 1))
    (S : SelectorState P h) (hq : (4 : ℝ) / 3 ≤ P.rawEnvelope h) :
    Nonempty (CheckpointCertificate P) ∨ ∃ s, h < s ∧ Nonempty (SelectorState P s) := by
  classical
  let q := P.rawEnvelope h
  have hq1 : 1 ≤ q := by dsimp [q]; linarith
  have hqpos : 0 < q := by linarith
  have hq3 : q < 3 := P.rawEnvelope_lt_three hP h (fun _ _ => Or.inl S.below_unit)
  obtain ⟨s, hs, hd, heq⟩ := P.rawEnvelope_attained h hqpos
  have hhs : h < s := (Finset.mem_filter.mp hs).2.1
  have ha : P.Active s := (Finset.mem_filter.mp hs).2.2
  have helig := P.attainer_suff_of_fourThirds hP h s hhs.le S.high.le S.credit
    q hq hq3 hd heq
  have henv := P.selector_envelope hP h
  by_cases hq2 : q ≤ 2
  · rcases P.actual_test hP h S.access q hq1 hq2 henv with hyes | hno
    · exact Or.inl hyes
    · have hf := hno s hhs ha (P.suff_implies_actual h s q helig)
      obtain ⟨hsafe, hhigh, _⟩ := P.fourThirds_profile_relay hP h s hhs S.high
        S.credit q hq hq2 hd heq hf
      right
      exact ⟨s, hhs, ⟨P.relayState hP h s S hhs ha hq1 hd heq hsafe hhigh
        (fun _ => hno) (fun hn => False.elim (not_lt_of_ge hq2 hn))
        (fun hn => False.elim (not_lt_of_ge hq hn))⟩⟩
  · rcases P.suff_test hP h S.access q (by linarith) hq3.le henv with hyes | hno
    · exact Or.inl hyes
    · have hf := hno s hhs ha helig
      obtain ⟨hsafe, hhigh, _⟩ := P.high_parameter_profile_relay hP h s hhs S.high
        S.credit q (by linarith) hd heq hf
      right
      exact ⟨s, hhs, ⟨P.relayState hP h s S hhs ha hq1 hd heq
        (fun z _ _ => (hsafe z).le) hhigh
        (fun hn => False.elim (hq2 hn)) (fun _ => hno)
        (fun hn => False.elim (not_lt_of_ge hq hn))⟩⟩

end
