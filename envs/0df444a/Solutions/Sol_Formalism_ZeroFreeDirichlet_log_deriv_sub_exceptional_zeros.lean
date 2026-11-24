-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_deriv_sub_exceptional_zeros
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:10.61803+00:00
-- url     : https://prove2.me/submissions/37101853-5fb9-4237-9ff3-63da6d1ee1a0

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogDerivSubExceptionalZeros

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {c₁ : ℝ} (hc₁ : 0 < c₁) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {B : Finset ℝ} (hχ : χ ≠ 1) (hBcard : B.card ≤ 1)
    (hBmem : ∀ β ∈ B, χ ≠ 1 ∧ InRegion c₁ q (β : ℂ) ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0 ∧
      deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0)
    (hBall : ∀ s : ℂ, InRegion c₁ q s → IsLZero χ s → ∃ β ∈ B, s = (β : ℂ))
    {s : ℂ} (hs : InRegion (c₁ / 2) q s) (hσ1 : 26 / 27 ≤ s.re) (hσ2 : s.re < 11 / 10)
    {Z : Finset ℂ} {m : ℂ → ℕ}
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) ∧
        DirichletCharacter.LFunction χ ρ = 0))
    (hm3 : ∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1)
    {K : ℝ}
    (hsum : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ K * Real.log ((q : ℝ) * (|s.im| + 2)) / Real.log 2)
    (hE : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ 1440 / 11 * (K * Real.log ((q : ℝ) * (|s.im| + 2)))) :
    ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤
      1440 / 11 * (K * Real.log ((q : ℝ) * (|s.im| + 2))) +
      3 * K / (c₁ * Real.log 2) * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 + 120 / 11 := by
  have hs' : 1 - c₁ / 2 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hs
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog2 : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set L := Real.log ((q : ℝ) * (|s.im| + 2)) with hLdef
  have hL2 : Real.log 2 ≤ L :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := hLpos.ne'
  have hfar : ∀ ρ ∈ Z, (∀ β ∈ B, ρ ≠ (β : ℂ)) → ‖1 / (s - ρ)‖ ≤ 3 * L / c₁ := by
    intro ρ hρ hne
    obtain ⟨hball, hzero⟩ := (hZ ρ).mp hρ
    have hnot : ¬ InRegion c₁ q ρ := by
      intro hreg
      obtain ⟨β, hβ, hρβ⟩ := hBall ρ hreg ⟨Or.inl hχ, hzero⟩
      exact hne β hβ hρβ
    simp only [InRegion, not_le] at hnot
    have him : |ρ.im - s.im| ≤ 11 / 60 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hball
      have h1 := Complex.abs_im_le_norm (ρ - ((21 / 20 : ℂ) + s.im * I))
      have hime : (ρ - ((21 / 20 : ℂ) + s.im * I)).im = ρ.im - s.im := by simp
      rw [hime] at h1
      linarith
    set Lρ := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLρdef
    have hLρ2 : Real.log 2 ≤ Lρ :=
      Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
    have hLρpos : 0 < Lρ := by linarith
    have hLρ : Lρ ≤ 6 / 5 * L := by
      have h1 : (q : ℝ) * (|ρ.im| + 2) ≤ (q : ℝ) * (|s.im| + 2) * (131 / 120) := by
        have h0 : |ρ.im| ≤ |s.im| + 11 / 60 := by
          have := abs_sub_abs_le_abs_sub ρ.im s.im
          linarith
        nlinarith [abs_nonneg s.im]
      have h2 : Lρ ≤ L + Real.log (131 / 120) := by
        rw [hLρdef, hLdef, ← Real.log_mul (by positivity) (by norm_num)]
        exact Real.log_le_log (by positivity) h1
      have h3 : Real.log (131 / 120) ≤ 131 / 120 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    have h1 : c₁ / (6 / 5 * L) ≤ c₁ / Lρ := div_le_div_of_nonneg_left hc₁.le hLρpos hLρ
    have h1' : c₁ / (6 / 5 * L) = 5 * c₁ / (6 * L) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    have h2 : c₁ / (3 * L) = 5 * c₁ / (6 * L) - c₁ / 2 / L := by
      field_simp
      ring
    have hre : c₁ / (3 * L) ≤ (s - ρ).re := by
      rw [Complex.sub_re]
      linarith
    have hpos : 0 < c₁ / (3 * L) := div_pos hc₁ (by linarith)
    have hnorm : c₁ / (3 * L) ≤ ‖s - ρ‖ := hre.trans (Complex.re_le_norm _)
    rw [norm_div, norm_one]
    calc 1 / ‖s - ρ‖ ≤ 1 / (c₁ / (3 * L)) := one_div_le_one_div_of_le hpos hnorm
      _ = 3 * L / c₁ := by rw [one_div_div]
  have hnear : ∀ β ∈ B, (β : ℂ) ∉ Z → ‖1 / (s - (β : ℂ))‖ ≤ 120 / 11 := by
    intro β hβ hβZ
    have hout : ¬ (β : ℂ) ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) := by
      intro hin
      exact hβZ ((hZ _).mpr ⟨hin, (hBmem β hβ).2.2.1⟩)
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hout
    have hsc : ‖s - ((21 / 20 : ℂ) + s.im * I)‖ ≤ 47 / 540 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have hre' : (s - ((21 / 20 : ℂ) + s.im * I)).re = s.re - 21 / 20 := by simp
      have him' : (s - ((21 / 20 : ℂ) + s.im * I)).im = 0 := by simp
      rw [hre', him', abs_zero, add_zero, abs_le]
      constructor <;> linarith
    have htri := norm_sub_le_norm_sub_add_norm_sub (β : ℂ) s ((21 / 20 : ℂ) + s.im * I)
    rw [norm_sub_rev (β : ℂ) s] at htri
    have hd : (11 : ℝ) / 120 ≤ ‖s - (β : ℂ)‖ := by linarith
    rw [norm_div, norm_one]
    calc 1 / ‖s - (β : ℂ)‖ ≤ 1 / (11 / 120) := one_div_le_one_div_of_le (by norm_num) hd
      _ = 120 / 11 := by norm_num
  have hmsum : ∀ Z' ⊆ Z, (∀ ρ ∈ Z', ∀ β ∈ B, ρ ≠ (β : ℂ)) →
      ‖∑ ρ ∈ Z', (m ρ : ℂ) / (s - ρ)‖ ≤ 3 * K / (c₁ * Real.log 2) * L ^ 2 := by
    intro Z' hZ' hne
    have hc3 : 0 ≤ 3 * L / c₁ := div_nonneg (by linarith) hc₁.le
    calc ‖∑ ρ ∈ Z', (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z', ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z', (m ρ : ℝ) * (3 * L / c₁) := Finset.sum_le_sum fun ρ hρ => by
          rw [div_eq_mul_one_div, norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (hfar ρ (hZ' hρ) (hne ρ hρ)) (Nat.cast_nonneg _)
      _ = (∑ ρ ∈ Z', (m ρ : ℝ)) * (3 * L / c₁) := by rw [Finset.sum_mul]
      _ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) * (3 * L / c₁) :=
          mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum_of_subset_of_nonneg hZ' fun _ _ _ => Nat.cast_nonneg _) hc3
      _ ≤ K * L / Real.log 2 * (3 * L / c₁) := mul_le_mul_of_nonneg_right hsum hc3
      _ = 3 * K / (c₁ * Real.log 2) * L ^ 2 := by ring
  have hdecomp : negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ)) =
      -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) +
        ((∑ β ∈ B, 1 / (s - (β : ℂ))) - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) := by
    unfold negLD
    ring
  have hdiff : ‖(∑ β ∈ B, 1 / (s - (β : ℂ))) - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
      3 * K / (c₁ * Real.log 2) * L ^ 2 + 120 / 11 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hBcard with h0 | h1
    · obtain rfl := Finset.card_eq_zero.mp h0
      rw [Finset.sum_empty, zero_sub, norm_neg]
      have h2 := hmsum Z subset_rfl (fun ρ _ β hβ => by simp at hβ)
      linarith
    · obtain ⟨β, rfl⟩ := Finset.card_eq_one.mp h1
      rw [Finset.sum_singleton]
      by_cases hβZ : (β : ℂ) ∈ Z
      · rw [← Finset.add_sum_erase Z _ hβZ,
          hm3 _ hβZ (hBmem β (Finset.mem_singleton_self β)).2.2.2, Nat.cast_one,
          sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
        have h2 := hmsum (Z.erase (β : ℂ)) (Finset.erase_subset _ _) (fun ρ hρ β' hβ' => by
          rw [Finset.mem_singleton] at hβ'
          subst hβ'
          exact Finset.ne_of_mem_erase hρ)
        linarith
      · refine (norm_sub_le _ _).trans ?_
        have h2 := hnear β (Finset.mem_singleton_self β) hβZ
        have h3 := hmsum Z subset_rfl (fun ρ hρ β' hβ' => by
          rw [Finset.mem_singleton] at hβ'
          subst hβ'
          exact fun h => hβZ (h ▸ hρ))
        linarith
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  linarith [hE, hdiff]
end Formalism.ZeroFreeDirichlet
