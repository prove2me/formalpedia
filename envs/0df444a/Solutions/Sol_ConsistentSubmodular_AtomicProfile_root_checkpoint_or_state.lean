-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.root_checkpoint_or_state
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:42.787845+00:00
-- url     : https://prove2.me/submissions/15a7386e-f802-4d4d-baa8-91bd5840e5f9

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SuffConstructor
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_VertexCheckpoint
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_rawEnvelope_attained
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_last_actual_partner
import Theorems.Thm_ConsistentSubmodular_root_failed_credit_relay
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_last_suff_partner
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_root_attainer_suff

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

theorem root_strongCredit (hP : P.Canonical) : P.StrongCredit 0 := by
  right
  rw [P.benchmark_zero hP, hP.1]
  norm_num

end AtomicProfile

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem envelope_valid_upper (hP : P.Canonical) (h t : Fin (m + 1)) (q : ℝ)
    (hq : P.rawEnvelope h ≤ q) (ht : t ∈ P.laterActive h) :
    0 ≤ P.envelopeSlack h q t := by
  classical
  have hv := P.rawEnvelope_valid hP h t ht
  have hd := P.raw_denominator_nonnegative h t (le_of_lt (Finset.mem_filter.mp ht).2.1)
  have hm := mul_nonneg (sub_nonneg.mpr hq) hd
  unfold envelopeSlack at *
  nlinarith only [hv, hm]

end AtomicProfile

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (hP : P.Canonical)
    (hstrict : ∀ t : Fin (m + 1), 0 < t → P.designated t < 1) :
    Nonempty (CheckpointCertificate P) ∨ ∃ h, Nonempty (SelectorState P h) := by
  classical
  by_cases hnonpos : P.rawEnvelope 0 ≤ 0
  · left
    exact ⟨P.checkpoint_of_nonpositive hP 0 (by rw [hP.1]; norm_num)
      (P.root_strongCredit hP) (P.rootAccess hP) hnonpos⟩
  have hrawpos : 0 < P.rawEnvelope 0 := lt_of_not_ge hnonpos
  obtain ⟨s, hs, hden, hatt⟩ := P.rawEnvelope_attained 0 hrawpos
  have hs0 : 0 < s := (Finset.mem_filter.mp hs).2.1
  have hsactive : P.Active s := (Finset.mem_filter.mp hs).2.2
  let q := max 1 (P.rawEnvelope 0)
  have hq1 : 1 ≤ q := le_max_left _ _
  have hrawq : P.rawEnvelope 0 ≤ q := le_max_right _ _
  have hq0 : 0 < q := by linarith
  have hq3 : q < 3 := by
    apply max_lt (by norm_num)
    apply P.rawEnvelope_lt_three hP 0
    intro t ht
    exact Or.inr (by rw [hP.1]; exact hstrict t (Finset.mem_filter.mp ht).2.1)
  have henv : ∀ t, 0 < t → P.Active t → 0 ≤ P.envelopeSlack 0 q t := by
    intro t ht ha
    exact P.envelope_valid_upper hP 0 t q hrawq
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, ha⟩)
  have hsuff : 0 ≤ P.suffEligibility 0 q s := by
    by_cases hraw1 : P.rawEnvelope 0 ≤ 1
    · have hqe : q = 1 := max_eq_left hraw1
      unfold suffEligibility
      rw [hqe, hP.1]
      have := hP.2 s 0
      nlinarith
    · have hqe : q = P.rawEnvelope 0 := max_eq_right (le_of_not_ge hraw1)
      rw [hqe]
      exact (P.root_attainer_suff hP s _ (hstrict s hs0) hden hatt).le
  obtain ⟨c, hc, hsc, hec, hlast⟩ := P.last_suff_partner 0 s q hs hsuff
  have hc0 : 0 < c := (Finset.mem_filter.mp hc).2.1
  by_cases hsuccess : q ≤ (3 : ℝ) / 2 ∨ 2 * q - 3 ≤ q * (P.benchmark c - 1)
  · left
    exact ⟨P.checkpoint_of_root_suff hP c hc0 q hq1 hq3.le hec henv
      (fun t ht ha => (hlast t ht ha).le) hsuccess⟩
  have hq15 : (3 : ℝ) / 2 < q := by
    by_contra hn
    exact hsuccess (Or.inl (le_of_not_gt hn))
  have hfail : q * (P.benchmark c - 1) < 2 * q - 3 := by
    by_contra hn
    exact hsuccess (Or.inr (le_of_not_gt hn))
  have hqeq : q = P.rawEnvelope 0 := by
    apply max_eq_right
    by_contra hn
    have : q = 1 := max_eq_left (le_of_not_ge hn)
    linarith
  have hfail_s : P.benchmark c - 1 < 2 - 3 / q := by
    have hid : q * (2 - 3 / q) = 2 * q - 3 := by field_simp
    nlinarith
  have hpersist := P.persistence_credit 0 s (Fin.zero_le _)
  rw [P.baseline_zero, hP.1] at hpersist
  have hmono := P.benchmark_monotone hP hsc
  have hattq : P.rawRatio 0 s = q := hatt.trans hqeq.symm
  have ha := (div_eq_iff (ne_of_gt hden)).mp hattq
  unfold rawNumerator at ha
  rw [hP.1] at ha hden
  have hroot := root_failed_credit_relay (1 - P.designated s)
    (P.designated s - P.residual 0 s) (P.benchmark s - 1) (P.benchmark c - 1) q
    (by linarith [hstrict s hs0]) (sub_nonneg.mpr (hP.2 s 0)) (by linarith)
    hq0 (by linarith) (by linarith) (by nlinarith only [ha]) hfail_s
  have hsafe : P.PessimisticSafeEdge 0 s := by
    intro z _ _
    have hh := hroot.2 z
    rw [hP.1]
    nlinarith only [hh]
  have hhigh : (3 : ℝ) / 4 < P.designated s := by
    have := hroot.2 1
    norm_num at this
    linarith
  have hfsuff : ∀ t, 0 < t → P.Active t → 0 ≤ P.suffEligibility 0 q t →
      q * (P.benchmark t - P.designated 0) <
        2 * P.designated 0 * q - 3 * (4 * P.designated 0 - 3) := by
    intro t _ ht he
    have htc : t ≤ c := by
      by_contra hn
      have := hlast t (lt_of_not_ge hn) ht
      linarith
    have hm := mul_le_mul_of_nonneg_left (P.benchmark_monotone hP htc) hq0.le
    rw [hP.1]
    nlinarith
  have finish
      (hfactual : q ≤ 2 → ∀ t, 0 < t → P.Active t → 0 ≤ P.actualEligibility 0 q t →
        q * (P.benchmark t - P.designated 0) <
          2 * P.designated 0 * q - 3 * (4 * P.designated 0 - 3)) :
      ∃ h, Nonempty (SelectorState P h) := by
    let H : RelayHistory P s := {
      parent := 0
      advances := hs0
      child_active := hsactive
      parameter := q
      parameter_ge_one := hq1
      parameter_lt_three := hq3
      parent_high := by rw [hP.1]; norm_num
      parent_access := P.rootAccess hP
      parent_credit := P.root_strongCredit hP
      envelope := henv
      denominator := by rwa [hP.1]
      attaining := hattq
      safe_edge := hsafe
      failed_actual := hfactual
      failed_suff := fun _ => hfsuff
      small_parameter_high_anchor := by intro _; rw [hP.1]; norm_num }
    exact ⟨s, ⟨{
      high := hhigh
      below_unit := hstrict s hs0
      access := H.child_access
      credit := H.child_credit hP
      history := H }⟩⟩
  by_cases hq2 : q ≤ 2
  · obtain ⟨a, ha, hsa, hea, hlastA⟩ :=
      P.last_actual_partner 0 s q hs (P.suff_implies_actual 0 s q hsuff)
    have ha0 : 0 < a := (Finset.mem_filter.mp ha).2.1
    by_cases hacredit : 2 * q - 3 ≤ q * (P.benchmark a - 1)
    · left
      let acc := P.rootAccess hP
      exact ⟨P.checkpoint_of_actual_middle hP 0 a ha0 q hq1 hq2 hea henv
        (fun t ht ha => (hlastA t ht ha).le) (by rw [hP.1]; nlinarith)
        acc.entry acc.initial acc.terminal acc.safe acc.pieces⟩
    · right
      apply finish
      intro _ t _ ht he
      have hta : t ≤ a := by
        by_contra hn
        have := hlastA t (lt_of_not_ge hn) ht
        linarith
      have hm := mul_le_mul_of_nonneg_left (P.benchmark_monotone hP hta) hq0.le
      rw [hP.1]
      linarith
  · right
    exact finish (fun h => False.elim (hq2 h))

end
