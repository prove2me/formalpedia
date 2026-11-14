-- Prove2me | solution 1 for ConsistentSubmodular.RelayHistory.deficient_domain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:27:50.401501+00:00
-- url     : https://prove2.me/submissions/73c17baf-7bc2-48d6-92b7-b7296eb1c3a2

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState
import Theorems.Thm_ConsistentSubmodular_high_anchor_attainer_eligible
import Theorems.Thm_ConsistentSubmodular_deficient_child_parent_domain

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

namespace ConsistentSubmodular

theorem relay_baseline_upgrade_identity (d₀ e W b k : ℝ)
    (hatt : (3 - k) * W = k * e + b + 3 * d₀) :
    (3 - k) * (b + W + e - 3 * (d₀ + e)) =
      (4 - k) * b - (2 - k) * (3 * d₀ + 3 * e) := by
  nlinarith only [hatt]

theorem relay_baseline_upgrade_high (d₀ e W b k : ℝ)
    (hd : 0 ≤ d₀) (he : 0 ≤ e) (hb : 0 ≤ b) (hk2 : 2 ≤ k) (hk3 : k < 3)
    (hatt : (3 - k) * W = k * e + b + 3 * d₀) :
    3 * (d₀ + e) ≤ b + W + e := by
  have h1 := mul_nonneg (show 0 ≤ 4 - k by linarith) hb
  have h2 := mul_nonneg (show 0 ≤ k - 2 by linarith) (show 0 ≤ 3 * d₀ + 3 * e by positivity)
  have hid := relay_baseline_upgrade_identity d₀ e W b k hatt
  have hprod : 0 ≤ (3 - k) * (b + W + e - 3 * (d₀ + e)) := by nlinarith only [hid, h1, h2]
  have := nonneg_of_mul_nonneg_right hprod (show 0 < 3 - k by linarith)
  linarith

end ConsistentSubmodular

end

section

open ConsistentSubmodular
open ConsistentSubmodular.RelayHistory
variable {m atomCount : ℕ} {P : AtomicProfile m atomCount} {h : Fin (m + 1)}

theorem solution (H : RelayHistory P h) (hP : P.Canonical)
    (hhigh : (3 : ℝ) / 4 < P.designated h)
    (hdef : P.baseline h < 3 * (1 - P.designated h)) :
    (4 : ℝ) / 3 < H.parameter ∧ H.parameter < 2 ∧
      1 - P.designated H.parent < 1 / 8 ∧
      0 ≤ P.suffEligibility H.parent H.parameter h := by
  let k := H.parameter
  let d₀ := 1 - P.designated H.parent
  let e := P.designated H.parent - P.designated h
  let W := P.designated h - P.residual H.parent h
  let b := (P.benchmark h - P.designated H.parent) - W
  have hd : 0 ≤ d₀ := sub_nonneg.mpr (P.designated_le_one hP _)
  have he : 0 ≤ e := sub_nonneg.mpr (P.designated_antitone hP H.advances.le)
  have hchild : d₀ + e ≤ 1 / 4 := by dsimp [d₀, e]; linarith
  have hL := P.strongCredit_baseline hP H.parent H.parent_high.le H.parent_credit
  have hLb : P.baseline H.parent ≤ b := by
    have := P.persistence_credit H.parent h H.advances.le
    dsimp [b, W]; linarith
  have hatt : (3 - k) * W = k * e + b + 3 * d₀ :=
    P.attaining_equation H.parent h k H.denominator H.attaining
  have hbdef : b + W + e < 3 * (d₀ + e) := by
    dsimp [b, W, e, d₀, AtomicProfile.benchmark]
    linarith only [hdef]
  have hk2 : k < 2 := by
    by_contra hn
    have hh := relay_baseline_upgrade_high d₀ e W b k hd he
      ((P.baseline_nonnegative _).trans hLb) (le_of_not_gt hn) H.parameter_lt_three hatt
    linarith
  have hfailed : k * (b + W) < 2 * (1 - d₀) * k - 3 * (1 - 4 * d₀) := by
    have helig : 0 ≤ P.actualEligibility H.parent k h := by
      by_cases hk4 : (4 : ℝ) / 3 ≤ k
      · apply P.suff_implies_actual
        have := attaining_suff_eligible (3 * d₀) e W b k (by positivity) he
          (by dsimp [d₀] at *; linarith) hk4 H.parameter_lt_three hatt
        exact this
      · have hanchor := H.small_parameter_high_anchor (lt_of_not_ge hk4)
        have hp : d₀ ≤ P.benchmark H.parent - 1 := by
          dsimp [d₀, AtomicProfile.benchmark] at *
          linarith
        have hh := high_anchor_attainer_eligible k (P.benchmark H.parent - 1) d₀ e W b
          H.parameter_ge_one hk2.le hd (by dsimp [d₀]; linarith) hp he
          (by dsimp [d₀, AtomicProfile.benchmark] at *; linarith) hatt
        convert hh using 1
        dsimp [AtomicProfile.actualEligibility, d₀, e, W]
        ring
    have hh := H.failed_actual hk2.le h H.advances H.child_active helig
    dsimp [k, b, d₀] at *
    nlinarith only [hh]
  obtain ⟨hk4, hk2, hd8⟩ := deficient_child_parent_domain d₀ e W b
    (P.baseline H.parent) k hd he hchild hL hLb H.parameter_ge_one H.parameter_lt_three
    hatt hbdef hfailed
  refine ⟨hk4, hk2, hd8, ?_⟩
  exact attaining_suff_eligible (3 * d₀) e W b k (by positivity) he
    (by dsimp [d₀] at *; linarith) hk4.le H.parameter_lt_three hatt

end
