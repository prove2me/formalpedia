-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.middle_parameter_checkpoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:32.988007+00:00
-- url     : https://prove2.me/submissions/db00e0ff-bf93-4c70-aae1-e8f0f07d7b37

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_MiddleCredits
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RollbackCheckpoint
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_rawEnvelope_attained
import Theorems.Thm_ConsistentSubmodular_RelayHistory_deficient_domain
import Theorems.Thm_ConsistentSubmodular_middle_three_credits
import Theorems.Thm_ConsistentSubmodular_MiddleRollback_all_later_suff_of_credits

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

namespace ConsistentSubmodular

theorem middle_child_elimination (q d p δ w P : ℝ) (hq4 : q ≤ 4)
    (hatt : P = (4 - q) * w - q * δ - 4 * d) (hper : p + w ≤ P) :
    0 ≤ (3 - q) * P - (4 - q) * p - q * δ - 4 * d := by
  have := mul_nonneg (sub_nonneg.mpr hq4) (sub_nonneg.mpr hper)
  rw [hatt] at *
  nlinarith only [this]

theorem middle_parent_I (k d₀ d p W : ℝ) (hk4 : k ≤ 4)
    (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hper : W + d₀ ≤ p) :
    0 ≤ (3 - k) * p - k * d - 2 * (4 - k) * d₀ := by
  have := mul_nonneg (sub_nonneg.mpr hk4) (sub_nonneg.mpr hper)
  nlinarith only [this, hatt]

theorem middle_parent_cutoff (k d₀ d p : ℝ)
    (_hk : (4 : ℝ) / 3 ≤ k) (_hk2 : k ≤ 2) (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4)
    (hpd : p ≤ 2 * d)
    (hI : 0 ≤ (3 - k) * p - k * d - 2 * (4 - k) * d₀)
    (hfailed : k * p ≤ 2 * k - 3 + 3 * (4 - k) * d₀) : (38 : ℝ) / 23 ≤ k := by
  by_cases hk9 : (9 : ℝ) / 5 ≤ k
  · linarith
  have h1 := mul_nonneg (show 0 ≤ 9 - 5 * k by linarith) (sub_nonneg.mpr hpd)
  have hupper : 0 ≤ 4 * k - 6 + (18 - 13 * k) * d := by
    nlinarith only [hI, hfailed, h1]
  by_cases hk18 : k ≤ 18 / 13
  · have h2 := mul_nonneg (show 0 ≤ 18 - 13 * k by linarith) (sub_nonneg.mpr hd4)
    nlinarith
  · have h2 := mul_nonneg (show 0 ≤ 13 * k - 18 by linarith) (sub_nonneg.mpr hd7)
    nlinarith

theorem middle_child_benchmark_floor (q d p δ P : ℝ)
    (hq1 : 1 ≤ q) (hq3 : q < 3) (hd : 0 ≤ d) (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hF : 0 ≤ (3 - q) * P - (4 - q) * p - q * δ - 4 * d) :
    0 ≤ 2 * P - 3 * p - 4 * d - δ := by
  have hqδ := mul_nonneg (show 0 ≤ q by linarith) hδ
  have hprod : 0 ≤ (3 - q) * (P - p) := by nlinarith only [hF, hqδ, hd, hp]
  have hPp := nonneg_of_mul_nonneg_right hprod (sub_pos.mpr hq3)
  have h1 := mul_nonneg (sub_nonneg.mpr hq1) (show 0 ≤ P - p + δ by linarith)
  nlinarith only [hF, h1]

end ConsistentSubmodular

end

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

set_option maxHeartbeats 1200000 in
theorem solution (hP : P.Canonical) (h : Fin (m + 1))
    (S : SelectorState P h) (hq1 : 1 ≤ P.rawEnvelope h)
    (hq4 : P.rawEnvelope h < (4 : ℝ) / 3) (hA : P.designated h < (33 : ℝ) / 40)
    (hL : P.baseline h < 3 * (1 - P.designated h))
    (hno : ∀ t, h < t → P.Active t → 0 ≤ P.actualEligibility h (P.rawEnvelope h) t →
      P.rawEnvelope h * (P.benchmark t - P.designated h)<
        2 * P.designated h * P.rawEnvelope h - 3 * (4 * P.designated h - 3)) :
    Nonempty (CheckpointCertificate P) := by
  classical
  let H := S.history
  let a := H.parent
  let k := H.parameter
  let q := P.rawEnvelope h
  let d₀ := 1 - P.designated a
  let d := 1 - P.designated h
  let p := P.benchmark h - 1
  let W := P.designated h - P.residual a h
  obtain ⟨hk4, hk2, hd08, helig⟩ := H.deficient_domain hP S.high hL
  have hd₀ : 0 ≤ d₀ := sub_nonneg.mpr (P.designated_le_one hP a)
  have hd7 : (7 : ℝ) / 40 ≤ d := by dsimp [d]; linarith
  have hd4 : d ≤ 1 / 4 := by dsimp [d]; linarith [S.high]
  have hparentatt : p = (4 - k) * W - k * d - (4 - k) * d₀ := by
    have hh := P.attaining_equation a h k H.denominator H.attaining
    dsimp [p, W, d, d₀, k, a] at *
    nlinarith only [hh]
  have hparentper : W + d₀ ≤ p := by
    have hp := P.persistence_credit a h H.advances.le
    have hbase := P.strongCredit_baseline hP a H.parent_high.le H.parent_credit
    dsimp [W, d₀, p]; linarith
  have hmid : d + 2 * d₀ ≤ W := by
    have hm := H.safe_edge (1 / 2) (by norm_num) (by norm_num)
    dsimp [d, d₀, W, a]
    nlinarith only [hm]
  have hpd : d ≤ p := by linarith
  have hp2d : p ≤ 2 * d := by dsimp [p, d, benchmark]; linarith
  have hparent : k * p ≤ 2 * k - 3 + 3 * (4 - k) * d₀ := by
    have hh := H.suff_failure h H.advances H.child_active helig
    dsimp [k, p, d₀, a]
    nlinarith only [hh]
  have hk0 : 0 < k := by dsimp [k]; linarith
  have hcredit : ∀ t, h ≤ t → LowRollback.Active P t → LowRollback.ParentEligible P a t k →
      LowRollback.shifted P t ≤ LowRollback.ceiling k d₀ := by
    intro t hht ha he
    have he' : 0 ≤ P.suffEligibility a k t := by
      dsimp [LowRollback.ParentEligible, LowRollback.deficit, LowRollback.gap] at he
      unfold suffEligibility
      dsimp [d₀, a, k] at *
      nlinarith only [he]
    have hf := H.suff_failure t (lt_of_lt_of_le H.advances hht) ha he'
    have hh : k * (P.benchmark t - 1) ≤ 2 * k - 3 + 3 * (4 - k) * d₀ := by
      dsimp [d₀, k, a]
      nlinarith only [hf]
    have hceq : LowRollback.ceiling k d₀ = (2 * k - 3 + 3 * (4 - k) * d₀) / k := by
      unfold LowRollback.ceiling
      field_simp
    rw [hceq]
    apply (le_div_iff₀ hk0).2
    dsimp [LowRollback.shifted]
    nlinarith only [hh]
  obtain ⟨s, hs, hden, hatt⟩ := P.rawEnvelope_attained h (by linarith)
  have hhs : h < s := (Finset.mem_filter.mp hs).2.1
  have hsactive : P.Active s := (Finset.mem_filter.mp hs).2.2
  let δ := P.designated h - P.designated s
  let w := P.designated s - P.residual h s
  let Ps := P.benchmark s - 1
  have hδ : 0 ≤ δ := sub_nonneg.mpr (P.designated_antitone hP hhs.le)
  have hatt' : Ps = (4 - q) * w - q * δ - 4 * d := by
    have hh := P.attaining_equation h s q hden hatt
    dsimp [Ps, q, w, δ, d]
    nlinarith only [hh]
  have hper : p + w ≤ Ps := by
    have hh := P.persistence_credit h s hhs.le
    dsimp [p, w, Ps, benchmark] at *
    linarith
  have hcap : w ≤ 1 - d - δ := by
    have hr := P.residual_nonnegative h s
    dsimp [w, d, δ]
    linarith
  have hfailed : 0 ≤ q * (2 - 3 * d - Ps) - 3 * (1 - 4 * d) := by
    by_cases he : 0 ≤ P.actualEligibility h q s
    · have hf := hno s hhs hsactive he
      dsimp [q, d, Ps]
      nlinarith only [hf]
    · have hh : 4 * P.actualEligibility h q s =
          q * (Ps + 3 * d - 2) + 3 * (1 - 4 * d) + (q - 1) * (3 * d + (q - 1) * (1 - d)) := by
        have hid := congrArg (fun x : ℝ => q * x) hatt'
        dsimp [actualEligibility, w, δ, d, Ps] at *
        nlinarith only [hid]
      have hterm : 0 ≤ (q - 1) * (3 * d + (q - 1) * (1 - d)) := by
        apply mul_nonneg (by dsimp [q]; linarith)
        have : 0 ≤ (q - 1) * (1 - d) := mul_nonneg (by dsimp [q]; linarith) (by linarith)
        linarith
      linarith only [hh, he, hterm]
  have hF := middle_child_elimination q d p δ w Ps (by dsimp [q]; linarith) hatt' hper
  have hLP := middle_child_benchmark_floor q d p δ Ps hq1 (by dsimp [q]; linarith)
    (by linarith) (by linarith) hδ hF
  have hCbound : middleCap k d₀ ≤ 1 / 2 + 3 * d₀ := by
    have hprod := mul_nonneg (show 0 ≤ 2 - k by dsimp [k]; linarith)
      (show 0 ≤ 3 / 2 - 6 * d₀ by dsimp [d₀, a]; linarith)
    have hceq : middleCap k d₀ = (2 * k - 3 + 3 * (4 - k) * d₀) / k := by
      unfold middleCap
      field_simp
    rw [hceq]
    apply (div_le_iff₀ hk0).2
    nlinarith only [hprod]
  have hsource : middleCap k d₀ < Ps := by linarith only [hLP, hδ, hmid, hparentper, hd7, hCbound, hd₀]
  have hscap : P.designated s - P.residual a s ≤ (k - 1) * (d + δ) + (4 - k) * d₀ := by
    by_contra hn
    have he : LowRollback.ParentEligible P a s k := by
      dsimp [LowRollback.ParentEligible, LowRollback.deficit, LowRollback.gap]
      dsimp [d, δ, d₀, a] at *
      linarith only [hn]
    have hh := hcredit s hhs.le hsactive he
    change Ps ≤ middleCap k d₀ at hh
    linarith only [hh, hsource]
  have hG : 0 ≤ k * (4 - k) * δ - p - (k - 2) ^ 2 * d + (4 - k) * (3 - k) * d₀ := by
    have hres := P.residual_antitone a hhs.le
    have hper' : W ≤ δ + (P.designated s - P.residual a s) := by
      dsimp [W, δ]
      linarith only [hres]
    have hmult := mul_nonneg (show 0 ≤ 4 - k by dsimp [k]; linarith)
      (show 0 ≤ k * δ - W + (k - 1) * d + (4 - k) * d₀ by nlinarith only [hscap, hper'])
    nlinarith only [hmult, hparentatt]
  obtain ⟨hU, hV, hZ⟩ := middle_three_credits k d₀ d p W q δ w Ps hk4.le hk2.le hd₀
    hd7 hd4 hpd hp2d hparentatt hparentper hparent hq1 hq4.le hδ hatt' hper hcap hfailed hG
  have hI := middle_parent_I k d₀ d p W (by dsimp [k]; linarith) hparentatt hparentper
  have hcut := middle_parent_cutoff k d₀ d p hk4.le hk2.le hd7 hd4 hp2d hI hparent
  have hrows := MiddleRollback.all_later_suff_of_credits P hP a h s (ne_of_lt H.advances)
    hhs.le k (by linarith only [hcut]) hk2.le hcredit
    (show 0 ≤ LowRollback.U k (LowRollback.deficit P a) (LowRollback.deficit P h)
      (LowRollback.shifted P h) (LowRollback.gap P a h) from hU.le)
    (by dsimp [LowRollback.V, LowRollback.deficit, LowRollback.shifted];
        dsimp [p, d, d₀, δ, a] at hV; convert hV using 1; ring)
    (by dsimp [LowRollback.deficit, LowRollback.shifted];
        dsimp [Ps, d, d₀, δ, a] at hZ; nlinarith only [hZ])
  exact ⟨P.checkpoint_of_rollback hP h H hk0.le (by linarith)
    helig hrows⟩

end
