-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.low_parameter_checkpoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:42.443786+00:00
-- url     : https://prove2.me/submissions/caecbaac-2839-4aa0-b12b-9cc2f98c0486

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SuffConstructor
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_rawEnvelope_attained
import Theorems.Thm_ConsistentSubmodular_LowRollback_all_later_suff_of_credits
import Theorems.Thm_ConsistentSubmodular_LowRollback_child_semantic_sources
import Theorems.Thm_ConsistentSubmodular_LowRollback_attainer_credit_exceeds
import Theorems.Thm_ConsistentSubmodular_LowRollback_source_exclusions
import Theorems.Thm_ConsistentSubmodular_LowRollback_source_parameter_upper
import Theorems.Thm_ConsistentSubmodular_LowRollback_before_low_credit
import Theorems.Thm_ConsistentSubmodular_LowRollback_before_high_credit
import Theorems.Thm_ConsistentSubmodular_LowRollback_eligible_low_credit
import Theorems.Thm_ConsistentSubmodular_LowRollback_eligible_high_credit
import Theorems.Thm_ConsistentSubmodular_LowRollback_after_credit

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

namespace RelayHistory

variable {P : AtomicProfile m atomCount} {child : Fin (m + 1)}

theorem suff_failure (H : RelayHistory P child) (t : Fin (m + 1))
    (ht : H.parent < t) (ha : P.Active t) (he : 0 ≤ P.suffEligibility H.parent H.parameter t) :
    H.parameter * (P.benchmark t - P.designated H.parent) <
      2 * P.designated H.parent * H.parameter - 3 * (4 * P.designated H.parent - 3) := by
  by_cases hq : H.parameter ≤ 2
  · exact H.failed_actual hq t ht ha (P.suff_implies_actual H.parent t H.parameter he)
  · exact H.failed_suff (lt_of_not_ge hq) t ht ha he

end RelayHistory

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace LowRollback

variable {m aCount : ℕ}

theorem deficit_monotone (P : AtomicProfile m aCount) (hP : P.Canonical) :
    Monotone (deficit P) := by
  intro s t hst
  exact sub_le_sub_left (P.designated_antitone hP hst) 1

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

theorem parentEligible_iff (P : AtomicProfile m aCount) (a t : Fin (m + 1)) (k : ℝ) :
    ParentEligible P a t k ↔ 0 ≤ P.suffEligibility a k t := by
  unfold ParentEligible AtomicProfile.suffEligibility deficit gap
  constructor <;> intro hi <;> nlinarith

theorem attainment_shifted (P : AtomicProfile m aCount) (a h : Fin (m + 1)) (k : ℝ)
    (hden : 0 < P.designated a - P.residual a h) (hatt : P.rawRatio a h = k) :
    shifted P h = (4 - k) * gap P a h - k * deficit P h - (4 - k) * deficit P a := by
  have heq := (div_eq_iff (ne_of_gt hden)).mp hatt
  unfold AtomicProfile.rawNumerator at heq
  unfold shifted deficit gap
  nlinarith only [heq]

theorem parent_floor_of_attainment (k d₀ d p W : ℝ)
    (hk4 : k ≤ 4) (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hp : W + d₀ ≤ p) : 0 ≤ parentFloor k d₀ d p := by
  have heq : parentFloor k d₀ d p = (4 - k) * (p - W - d₀) := by
    unfold parentFloor
    nlinarith only [hatt]
  rw [heq]
  exact mul_nonneg (sub_nonneg.mpr hk4) (by linarith)

theorem strong_credit_weak (d p : ℝ) (hd : d ≤ 1 / 4) (_hp : 0 ≤ p)
    (hstrong : 1 / 2 ≤ p ∨ d ≤ p * (1 - p)) : d ≤ p := by
  rcases hstrong with h | h
  · linarith
  · nlinarith [sq_nonneg p]

theorem eliminated_child_floor (q d p δ P : ℝ) (hq0 : 0 ≤ q) (hq3 : q ≤ 3)
    (hF : 0 ≤ childPersistence q d p δ P) (hJ : 0 ≤ childIneligibility q d P) :
    0 ≤ cpoly q * d - npoly q - apoly q * p - q ^ 2 * δ := by
  have heq : cpoly q * d - npoly q - apoly q * p - q ^ 2 * δ =
      q * childPersistence q d p δ P + (3 - q) * childIneligibility q d P := by
    unfold cpoly npoly apoly childPersistence childIneligibility
    ring
  rw [heq]
  exact add_nonneg (mul_nonneg hq0 hF) (mul_nonneg (sub_nonneg.mpr hq3) hJ)

theorem child_capacity_floor (q d p δ P : ℝ) (hq3 : q ≤ 3)
    (hF : 0 ≤ childPersistence q d p δ P) (hK : 0 ≤ childCapacity q d δ P) :
    0 ≤ (3 - q) * (1 - d) - 4 * d - p - 3 * δ := by
  have h4 : 0 < 4 - q := by linarith
  have heq : (4 - q) * ((3 - q) * (1 - d) - 4 * d - p - 3 * δ) =
      (3 - q) * childCapacity q d δ P + childPersistence q d p δ P := by
    unfold childCapacity childPersistence
    ring
  apply (mul_nonneg_iff_of_pos_left h4).mp
  rw [heq]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hq3) hK) hF

theorem child_deficit_floor (q d p δ P : ℝ) (hq0 : 0 ≤ q) (hq3 : q ≤ 3)
    (hF : 0 ≤ childPersistence q d p δ P) (hK : 0 ≤ childCapacity q d δ P)
    (hJ : 0 ≤ childIneligibility q d P) :
    0 ≤ (5 - 3 * q) * d - p - dpoly q * δ := by
  have hcap := child_capacity_floor q d p δ P hq3 hF hK
  have hchild := eliminated_child_floor q d p δ P hq0 hq3 hF hJ
  have heq : 4 * ((5 - 3 * q) * d - p - dpoly q * δ) =
      (q - 2) ^ 2 * ((3 - q) * (1 - d) - 4 * d - p - 3 * δ) + (cpoly q * d - npoly q - apoly q * p - q ^ 2 * δ) := by
    unfold dpoly cpoly npoly apoly
    ring
  have hprod := mul_nonneg (sq_nonneg (q - 2)) hcap
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

private theorem parent_attainer_eligible (k d₀ d p W : ℝ)
    (hk0 : 4 / 3 ≤ k) (hk3 : k < 3) (hd₀ : 0 ≤ d₀) (hd₀d : d₀ ≤ d)
    (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀) (hweak : W + d₀ ≤ p) :
    (k - 1) * d + (4 - k) * d₀ ≤ W := by
  have hi : (3 - k) * (W - (k - 1) * d - (4 - k) * d₀) =
      (p - W - d₀) + (k ^ 2 - 3 * k + 3) * (d - d₀) + (3 * k - 4) * d₀ := by rw [hatt]; ring
  have h1 : 0 ≤ p - W - d₀ := by linarith
  have h2 := mul_nonneg (show 0 ≤ k ^ 2 - 3 * k + 3 by nlinarith [sq_nonneg (k - 3 / 2)])
    (sub_nonneg.mpr hd₀d)
  have h3 := mul_nonneg (show 0 ≤ 3 * k - 4 by linarith) hd₀
  have hh : 0 ≤ (3 - k) * (W - (k - 1) * d - (4 - k) * d₀) := by rw [hi]; linarith
  have := (mul_nonneg_iff_of_pos_left (show 0 < 3 - k by linarith)).mp hh
  linarith

private theorem history_ceiling (P : AtomicProfile m aCount) (h : Fin (m + 1))
    (H : RelayHistory P h) (t : Fin (m + 1)) (hat : H.parent < t)
    (ht : P.Active t) (he : ParentEligible P H.parent t H.parameter) :
    shifted P t < ceiling H.parameter (deficit P H.parent) := by
  have hf := H.suff_failure t hat ht ((parentEligible_iff P H.parent t H.parameter).mp he)
  have hk : 0 < H.parameter := lt_of_lt_of_le zero_lt_one H.parameter_ge_one
  have hc : H.parameter * ceiling H.parameter (deficit P H.parent) =
      2 * H.parameter - 3 + 3 * (4 - H.parameter) * deficit P H.parent := by
    unfold ceiling
    field_simp
  have hh : H.parameter * shifted P t < H.parameter * ceiling H.parameter (deficit P H.parent) := by
    dsimp [shifted, deficit] at *
    nlinarith only [hf, hc]
  nlinarith only [hh, hk]

end LowRollback

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.LowRollback
variable {m aCount : ℕ}

theorem solution (P : AtomicProfile m aCount) (hP : P.Canonical)
    (h : Fin (m + 1)) (state : SelectorState P h)
    (hparent : 4 / 3 ≤ state.history.parameter)
    (hanchor : P.designated h < 1281 / 1600)
    (hq0 : 0 < P.rawEnvelope h) (hq1 : P.rawEnvelope h ≤ 1)
    (hno : ∀ t, h < t → P.Active t → P.actualEligibility h (P.rawEnvelope h) t < 0) :
    Nonempty (CheckpointCertificate P) := by
  classical
  let H := state.history
  let a := H.parent
  let k := H.parameter
  let q := P.rawEnvelope h
  let d₀ := deficit P a
  let d := deficit P h
  let p := shifted P h
  let pa := shifted P a
  let W := gap P a h
  have hak : a < h := H.advances
  have hk0 : 4 / 3 ≤ k := hparent
  have hk3 : k < 3 := H.parameter_lt_three
  have hkpos : 0 < k := by linarith
  have hk4 : k ≤ 4 := by linarith
  have hd₀ : 0 ≤ d₀ := sub_nonneg.mpr (P.designated_le_one hP a)
  have hd₀hi : d₀ ≤ 1 / 4 := by dsimp [d₀, deficit]; have := H.parent_high; linarith
  have hd : 319 / 1600 < d := by dsimp [d, deficit]; linarith
  have hdhi : d ≤ 1 / 4 := by dsimp [d, deficit]; have := state.high; linarith
  have hd₀d : d₀ ≤ d := deficit_monotone P hP hak.le
  have hpa : 0 ≤ pa := sub_nonneg.mpr (P.one_le_benchmark hP a)
  have hp : 0 ≤ p := sub_nonneg.mpr (P.one_le_benchmark hP h)
  have hstrong : 1 / 2 ≤ pa ∨ d₀ ≤ pa * (1 - pa) := H.parent_credit
  have hpweak : d₀ ≤ pa := strong_credit_weak d₀ pa hd₀hi hpa hstrong
  have hpW : W + pa ≤ p := by
    have hs := carrier_persistence P a h hak.le
    change 0 ≤ p - pa - W at hs
    linarith
  have hweak : W + d₀ ≤ p := by linarith
  have hatt : p = (4 - k) * W - k * d - (4 - k) * d₀ := attainment_shifted P a h k H.denominator H.attaining
  have hI := parent_floor_of_attainment k d₀ d p W hk4 hatt hweak
  have helig : ParentEligible P a h k := parent_attainer_eligible k d₀ d p W hk0 hk3 hd₀ hd₀d hatt hweak
  have hpc : p < ceiling k d₀ := history_ceiling P h H h hak H.child_active helig
  have hcredit : ∀ t, h ≤ t → Active P t → ParentEligible P a t k →
      shifted P t ≤ ceiling k d₀ := by
    intro t hht ht he
    exact (history_ceiling P h H t (hak.trans_le hht) ht he).le
  have hku : k < 40 / 17 := source_parameter_upper k d₀ d p hk0 hk3 hd.le hd₀ hI hpc
  obtain ⟨s, hs, hden, hseq⟩ := P.rawEnvelope_attained h hq0
  have hhs : h < s := (Finset.mem_filter.mp hs).2.1
  have hsactive : P.Active s := (Finset.mem_filter.mp hs).2.2
  let δ := deficit P s - deficit P h
  let Ps := shifted P s
  have hδ : 0 ≤ δ := sub_nonneg.mpr (deficit_monotone P hP hhs.le)
  have hPs : p ≤ Ps := by
    have hh := P.benchmark_monotone hP hhs.le
    dsimp [p, Ps, shifted]
    linarith
  obtain ⟨hF, hK, hJ⟩ := child_semantic_sources P hP h s hhs.le q (by dsimp [q]; linarith)
    hden hseq (hno s hhs hsactive).le
  change 0 ≤ childPersistence q d p δ Ps at hF
  change 0 ≤ childCapacity q d δ Ps at hK
  change 0 ≤ childIneligibility q d Ps at hJ
  have hElim := eliminated_child_floor q d p δ Ps hq0.le (by dsimp [q]; linarith) hF hJ
  have hChild : 0 ≤ cpoly q * d - npoly q - apoly q * p := by
    have hm := mul_nonneg (sq_nonneg q) hδ
    linarith
  have hParent : 0 ≤ (3 - k) * p - k * d - (4 - k) * (d₀ + pa) := by
    have hid : (3 - k) * p - k * d - (4 - k) * (d₀ + pa) = (4 - k) * (p - W - pa) := by rw [hatt]; ring
    rw [hid]
    exact mul_nonneg (by linarith) (by linarith)
  have hCredit : 0 ≤ 2 * k - 3 + 3 * (4 - k) * d₀ - k * p := by
    have hc : k * ceiling k d₀ = 2 * k - 3 + 3 * (4 - k) * d₀ := by unfold ceiling; field_simp
    have hm := mul_lt_mul_of_pos_left hpc hkpos
    linarith
  have hdomain : 40 / 23 < k ∧ 20 - 11 * k + (2 * k - 5) * q < 0 := by
    by_cases hkle : k ≤ 20 / 11
    · exact source_exclusions k q d₀ d p pa hk0 hkle hq0.le hq1 hpa hd₀ hd₀hi
        hstrong hParent hCredit hChild
    · refine ⟨by linarith, ?_⟩
      have hm := mul_neg_of_neg_of_pos (show 2 * k - 5 < 0 by linarith) hq0
      nlinarith
  have hR := child_deficit_floor q d p δ Ps hq0.le (by dsimp [q]; linarith) hF hK hJ
  have hU : 0 ≤ U k d₀ d p W := by
    by_cases hkle : k ≤ 20 / 11
    · exact (eligible_low_credit k d₀ d p W hdomain.1.le hkle hd.le hd₀ hd₀d hatt hweak).le
    · exact (eligible_high_credit k q d₀ d p W (by linarith) hk3 hq0 hq1 hd₀ hd₀d
        hd.le hdhi hatt hweak hpc.le hChild).le
  have hV : k ≤ 2 → 0 ≤ V k d₀ d p δ := by
    intro _
    exact (before_low_credit k q d₀ d p δ hk3 hq0 hq1 (by linarith) hd₀ hdomain.2 hI hR).le
  have hVh : 2 ≤ k → 0 ≤ VHigh k d₀ d p δ := by
    intro hk2
    exact (before_high_credit k q d₀ d p δ hk2 hk3 hq0 hq1 (by linarith) hd₀ hδ hI hR hElim).le
  have hY : 0 ≤ Y k d₀ d p δ Ps :=
    (after_credit k q d₀ d p δ Ps hdomain.1 hku hq0 hq1 hdomain.2 hd₀ hδ hI hF hK hJ).le
  have hPsC : ceiling k d₀ < Ps := attainer_credit_exceeds k q d₀ d p δ Ps hdomain.1 hk3 hq0.le
    (by linarith) hd₀ hδ hPs hI hF
  have hlate := all_later_suff_of_credits P hP a h s (ne_of_lt hak) hhs.le k
    (by linarith [hdomain.1]) hk3 hsactive hPsC hcredit hU hV hVh hY
  have hparenteligible : 0 ≤ P.suffEligibility a k h := (parentEligible_iff P a h k).mp helig
  have hstages : ∀ t, (3 : ℝ) / 4 * P.benchmark t ≤
      P.value t (mix (vertex a) (vertex h) (k / 4)) := by
    intro t
    by_cases hht : h ≤ t
    · exact (hlate t hht).trans (P.value_mix_vertices_sufficient t a h (ne_of_lt hak)
        (by positivity) (by linarith) (le_min (P.overlap_le_left a h t) (P.overlap_le_right a h t)))
    · by_cases ht : P.Active t
      · apply P.suff_pair_prefix a h t (ne_of_lt hak) k hkpos.le hk4 (le_of_not_ge hht) hparenteligible
        by_cases hat : a < t
        · exact H.envelope t hat ht
        · exact P.envelopeSlack_early hP a t k (le_of_not_gt hat)
      · exact P.inactive_stage_safe t
          ((simplex_vertex a).mix (simplex_vertex h) (by positivity) (by linarith)) (le_of_not_gt ht)
  obtain ⟨ex, hex0, hex1, hexsafe, hexpieces⟩ := P.suff_terminal_exit hP a h (k / 4)
    (by positivity) (by linarith) (hlate (Fin.last m) (Fin.le_last h))
  let en := H.parent_access.entry
  let finalEntry := PolygonalPath.segment (vertex a) (mix (vertex a) (vertex h) (k / 4))
  have hjoin : en.node (Fin.last en.pieces) = finalEntry.node 0 := H.parent_access.terminal
  refine ⟨{
    point := mix (vertex a) (vertex h) (k / 4)
    entry := PolygonalPath.append en finalEntry
    exit := ex
    simplex := (simplex_vertex a).mix (simplex_vertex h) (by positivity) (by linarith)
    support := supportCard_mix_vertices _ _ _
    stages := hstages
    entry_initial := by rw [PolygonalPath.append_initial]; exact H.parent_access.initial
    entry_terminal := by rw [PolygonalPath.append_terminal _ _ hjoin]; exact PolygonalPath.segment_terminal _ _
    exit_initial := hex0
    exit_terminal := hex1
    entry_safe := H.parent_access.safe.append
      (P.suff_pair_entry hP a h hak k hkpos.le hk4 hparenteligible) hjoin
    exit_safe := hexsafe
    piece_budget := ?_ }⟩
  change en.pieces + 1 + ex.pieces ≤ (m + 1) + 2
  have hp := H.parent_access.pieces
  have ha := a.isLt
  dsimp [en, a] at *
  omega

end
