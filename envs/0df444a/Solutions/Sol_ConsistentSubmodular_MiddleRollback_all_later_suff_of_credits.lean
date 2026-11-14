-- Prove2me | solution 1 for ConsistentSubmodular.MiddleRollback.all_later_suff_of_credits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:19.285366+00:00
-- url     : https://prove2.me/submissions/d9342458-88f7-4259-a9ba-8ee013b7bd42

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets
import Theorems.Thm_ConsistentSubmodular_LowRollback_before_low_margin

section

noncomputable section

namespace ConsistentSubmodular

namespace LowRollback

variable {m aCount : ℕ}

theorem gap_le_designated (P : AtomicProfile m aCount) (i t : Fin (m + 1)) :
    gap P i t ≤ P.designated t := sub_le_self _ (P.residual_nonnegative i t)

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

theorem eligible_margin (k d₀ d p W Δ Pt z u : ℝ)
    (hk0 : 0 ≤ k) (hk3 : k ≤ 3) (hΔ : 0 ≤ Δ)
    (hcredit : Pt ≤ ceiling k d₀) (hp : 0 ≤ Pt - p - u) (hW : 0 ≤ Pt - p - z + W) :
    U k d₀ d p W ≤ M₁ k (d + Δ) Pt z u := by
  have h1 := mul_nonneg (sub_nonneg.mpr hk3) hW
  have h2 := mul_nonneg hk0 hp
  unfold U M₁
  nlinarith

theorem margin_one_suff_lower (P : AtomicProfile m aCount) (a h t : Fin (m + 1))
    (_hah : a ≠ h) (k : ℝ) (_hk0 : 0 ≤ k) (_hk4 : k ≤ 4) :
    M₁ k (deficit P t) (shifted P t) (gap P a t) (gap P h t) ≤
      4 * (suffRow P a h t k - (3 : ℝ) / 4 * P.benchmark t) := by
  have hm := min_le_left (P.residual a t) (P.residual h t)
  unfold M₁ suffRow deficit shifted gap AtomicProfile.benchmark
  nlinarith

theorem margin_two_suff_lower (P : AtomicProfile m aCount) (a h t : Fin (m + 1))
    (_hah : a ≠ h) (k : ℝ) (_hk0 : 0 ≤ k) (_hk4 : k ≤ 4) :
    M₂ k (deficit P t) (shifted P t) (gap P a t) (gap P h t) ≤
      4 * (suffRow P a h t k - (3 : ℝ) / 4 * P.benchmark t) := by
  have hm := min_le_right (P.residual a t) (P.residual h t)
  unfold M₂ suffRow deficit shifted gap AtomicProfile.benchmark
  nlinarith

theorem baseline_le_suffRow (P : AtomicProfile m aCount) (a h t : Fin (m + 1))
    (k : ℝ) (hk0 : 0 ≤ k) (hk4 : k ≤ 4) : P.baseline t ≤ suffRow P a h t k := by
  have hm : 0 ≤ min (P.residual a t) (P.residual h t) :=
    le_min (P.residual_nonnegative a t) (P.residual_nonnegative h t)
  have h1 := mul_le_mul_of_nonneg_left (min_le_left (P.residual a t) (P.residual h t))
    (show 0 ≤ 1 - k / 4 by linarith)
  have h2 := mul_le_mul_of_nonneg_left (min_le_right (P.residual a t) (P.residual h t))
    (show 0 ≤ k / 4 by positivity)
  unfold suffRow
  nlinarith

end LowRollback

end ConsistentSubmodular

end

end

section

namespace ConsistentSubmodular

namespace MiddleRollback

open LowRollback

theorem after_margin (k d₀ d δ P Δ Pt z u : ℝ)
    (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hΔ : δ ≤ Δ)
    (hPt : P ≤ Pt) (hcap : z ≤ (k - 1) * (d + Δ) + (4 - k) * d₀)
    (hres : u ≤ 1 - (d + Δ)) :
    P - (k - 1) + (k - 2) ^ 2 * (d + δ) - (4 - k) ^ 2 * d₀ ≤ M₂ k (d + Δ) Pt z u := by
  have h1 := mul_nonneg (sub_nonneg.mpr hk1) (sub_nonneg.mpr hres)
  have h2 := mul_nonneg (show 0 ≤ 4 - k by linarith) (sub_nonneg.mpr hcap)
  have h3 := mul_nonneg (sq_nonneg (k - 2)) (sub_nonneg.mpr hΔ)
  unfold M₂
  nlinarith only [h1, h2, h3, hPt]

end MiddleRollback

end ConsistentSubmodular

end

section

open ConsistentSubmodular
open ConsistentSubmodular.MiddleRollback
open LowRollback
variable {m atomCount : ℕ}

theorem solution (P : AtomicProfile m atomCount) (hP : P.Canonical)
    (a h s : Fin (m + 1)) (hah : a ≠ h) (_hhs : h ≤ s)
    (k : ℝ) (hk : 3 / 2 ≤ k) (hk2 : k ≤ 2)
    (hcredit : ∀ t, h ≤ t → Active P t → ParentEligible P a t k →
      shifted P t ≤ ceiling k (deficit P a))
    (hU : 0 ≤ U k (deficit P a) (deficit P h) (shifted P h) (gap P a h))
    (hV : 0 ≤ V k (deficit P a) (deficit P h) (shifted P h)
      (deficit P s - deficit P h))
    (hZ : 0 ≤ shifted P s - (k - 1) + (k - 2) ^ 2 * deficit P s - (4 - k) ^ 2 * deficit P a) :
    ∀ t, h ≤ t → (3 : ℝ) / 4 * P.benchmark t ≤ suffRow P a h t k := by
  have hk0 : 0 ≤ k := by linarith
  have hk4 : k ≤ 4 := by linarith
  intro t hht
  by_cases hactive : Active P t
  · have h1 := margin_one_suff_lower P a h t hah k hk0 hk4
    have h2 := margin_two_suff_lower P a h t hah k hk0 hk4
    have hp := carrier_persistence P h t hht
    let Δ := deficit P t - deficit P h
    have hΔ : 0 ≤ Δ := sub_nonneg.mpr (deficit_monotone P hP hht)
    have hd : deficit P h + Δ = deficit P t := by dsimp [Δ]; ring
    by_cases he : ParentEligible P a t k
    · have hW := cross_row_persistence P a h t hht
      have hm := eligible_margin k (deficit P a) (deficit P h) (shifted P h)
        (gap P a h) Δ (shifted P t) (gap P a t) (gap P h t)
        hk0 (by linarith) hΔ (hcredit t hht hactive he) hp hW
      rw [hd] at hm
      linarith
    · have hcap : gap P a t ≤ (k - 1) * (deficit P h + Δ) + (4 - k) * deficit P a := by
        rw [hd]
        exact le_of_lt (lt_of_not_ge he)
      by_cases hts : t ≤ s
      · have hδ : Δ ≤ deficit P s - deficit P h :=
          sub_le_sub_right (deficit_monotone P hP hts) _
        have hm := before_low_margin k (deficit P a) (deficit P h) (shifted P h)
          (deficit P s - deficit P h) Δ (shifted P t) (gap P a t) (gap P h t)
          hk hk2 hδ hp hcap
        rw [hd] at hm
        have hu := max_le h1 h2
        linarith
      · have hst : s ≤ t := le_of_not_ge hts
        have hδ : deficit P s - deficit P h ≤ Δ :=
          sub_le_sub_right (deficit_monotone P hP hst) _
        have hPt : shifted P s ≤ shifted P t := sub_le_sub_right (P.benchmark_monotone hP hst) _
        have hres : gap P h t ≤ 1 - (deficit P h + Δ) := by
          rw [hd]
          simpa only [deficit, sub_sub_cancel] using gap_le_designated P h t
        have hm := after_margin k (deficit P a) (deficit P h)
          (deficit P s - deficit P h) (shifted P s) Δ (shifted P t)
          (gap P a t) (gap P h t) (by linarith) hk4 hδ hPt hcap hres
        rw [hd, add_sub_cancel] at hm
        linarith
  · have hbase : (3 : ℝ) / 4 * P.benchmark t ≤ P.baseline t := by
      have hh : 3 * P.designated t ≤ P.baseline t := le_of_not_gt hactive
      unfold AtomicProfile.benchmark
      linarith
    exact hbase.trans (baseline_le_suffRow P a h t k hk0 hk4)

end
