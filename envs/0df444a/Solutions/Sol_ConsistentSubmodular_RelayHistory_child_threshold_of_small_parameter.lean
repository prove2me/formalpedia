-- Prove2me | solution 1 for ConsistentSubmodular.RelayHistory.child_threshold_of_small_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:55.370535+00:00
-- url     : https://prove2.me/submissions/e6b5637e-0a07-4613-95ee-131d4b5b0ba8

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_high_anchor_profile_eligible

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

theorem small_parent_drop_bound (d p e w b k : ℝ)
    (_hd : 0 ≤ d) (hd7 : d ≤ 7 / 40) (hpd : d ≤ p)
    (hk1 : 1 ≤ k) (hk4 : k ≤ 4 / 3) (hb : p + d ≤ b)
    (hatt : (3 - k) * w = k * e + b + 3 * d)
    (hfail : k * (b + w) < 2 * (1 - d) * k - 3 * (1 - 4 * d)) :
    e < -5 / 16 + (9 / 2 : ℝ) * d - 2 * p := by
  have hk : 0 < k := by linarith
  have h3 : 0 < 3 - k := by linarith
  have h4 : 0 ≤ 4 - k := by linarith
  let a := 27 / 16 + (3 / 2 : ℝ) * d - 3 * p
  let atop := 27 / 16 - (3 / 2 : ℝ) * d
  have htop : 0 ≤ atop := by dsimp [atop]; linarith
  have hka := mul_nonneg hk.le (sub_nonneg.mpr hpd)
  have hkt := mul_nonneg (show 0 ≤ 4 / 3 - k by linarith) htop
  have hfactor : 0 ≤ (27 / 4 : ℝ) * (1 - 4 * d) - k * a := by
    dsimp [a, atop] at *
    nlinarith only [hka, hkt, hd7]
  have hdiff := mul_nonneg (show 0 ≤ 4 / 3 - k by linarith) hfactor
  have hfail' := mul_lt_mul_of_pos_left hfail h3
  have hatt' := congrArg (fun x : ℝ => k * x) hatt
  have hb' := mul_nonneg (mul_nonneg hk.le h4) (sub_nonneg.mpr hb)
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  dsimp [a] at hdiff
  nlinarith only [hdiff, hfail', hatt', hb', hk2]

/-- A rational comparison sufficient for the low-envelope eligibility test. -/
theorem small_parent_rational_floor (d p : ℝ)
    (_hd : 0 ≤ d) (hd7 : d ≤ 7 / 40) (_hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p)) :
    (1281 : ℝ) / 1600 < 21 / 16 - (11 / 2 : ℝ) * d + 2 * p := by
  by_cases hp91 : 91 / 400 ≤ p
  · linarith
  · have hc : d ≤ p * (1 - p) := by
      rcases hcredit with h | h
      · linarith
      · exact h
    have hfac : 0 ≤ (7 / 2 : ℝ) - (11 / 2 : ℝ) * (p + 91 / 400) := by linarith
    have hm := mul_nonneg (show 0 ≤ 91 / 400 - p by linarith) hfac
    nlinarith only [hm, hc]

/-- A failed relay from a high anchor with parameter at most four thirds
cannot enter the no-eligibility low-parameter rollback case. -/
theorem small_parent_child_threshold (d p e w b k : ℝ)
    (hd : 0 ≤ d) (hd7 : d ≤ 7 / 40) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hk1 : 1 ≤ k) (hk4 : k ≤ 4 / 3) (hb : p + d ≤ b)
    (hatt : (3 - k) * w = k * e + b + 3 * d)
    (hfail : k * (b + w) < 2 * (1 - d) * k - 3 * (1 - 4 * d)) :
    (1281 : ℝ) / 1600 < 1 - d - e := by
  have hpd : d ≤ p := by
    rcases hcredit with h | h
    · linarith
    · nlinarith [sq_nonneg p]
  have hdrop := small_parent_drop_bound d p e w b k hd hd7 hpd hk1 hk4 hb hatt hfail
  have hfloor := small_parent_rational_floor d p hd hd7 hp hcredit
  linarith

end ConsistentSubmodular

end

section

open ConsistentSubmodular
open ConsistentSubmodular.RelayHistory
variable {m atomCount : ℕ} {P : AtomicProfile m atomCount} {h : Fin (m + 1)}

theorem solution (H : RelayHistory P h) (hP : P.Canonical)
    (hk : H.parameter < 4 / 3) : (1281 : ℝ) / 1600 < P.designated h := by
  have hA := H.small_parameter_high_anchor hk
  have helig := P.high_anchor_profile_eligible hP H.parent h H.advances.le hA
    H.parent_credit H.parameter H.parameter_ge_one (by linarith) H.denominator H.attaining
  have hf := H.failed_actual (by linarith) h H.advances H.child_active helig
  have hb := P.persistence_credit H.parent h H.advances.le
  have hatt := P.attaining_equation H.parent h H.parameter H.denominator H.attaining
  have hh := small_parent_child_threshold (1 - P.designated H.parent)
    (P.benchmark H.parent - 1) (P.designated H.parent - P.designated h)
    (P.designated h - P.residual H.parent h)
    ((P.benchmark h - P.designated H.parent) - (P.designated h - P.residual H.parent h))
    H.parameter (by linarith [P.designated_le_one hP H.parent]) (by linarith)
    (by linarith [P.one_le_benchmark hP H.parent]) H.parent_credit
    H.parameter_ge_one hk.le (by unfold AtomicProfile.benchmark at *; linarith)
    hatt (by nlinarith only [hf])
  linarith

end
