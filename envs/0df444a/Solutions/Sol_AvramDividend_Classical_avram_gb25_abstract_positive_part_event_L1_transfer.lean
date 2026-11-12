-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb25_abstract_positive_part_event_L1_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:02:02.885657+00:00
-- url     : https://prove2.me/submissions/e5b61904-04cf-4732-ad14-85952f643720

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (F N Occ : Ω → ℝ)
    (M : ℕ → Ω → ℝ) (B c : ℝ)
    (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hFI : ∀ m, IntegrableOn (fun ω => max (F ω - M m ω) 0) A P)
    (hOccI : IntegrableOn Occ A P)
    (hErrI : ∀ m, IntegrableOn (fun ω => |N ω - M m ω|) A P)
    (hOccNonneg : ∀ᵐ ω ∂(P.restrict A), 0 ≤ Occ ω)
    (hBudget : ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ N ω + B + c * Occ ω)
    (hL1 : Tendsto (fun m : ℕ =>
      ∫ ω in A, |N ω - M m ω| ∂P) atTop (𝓝 (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ K : ℕ, ∃ m : ℕ, K < m ∧
      (∫ ω in A, max (F ω - M m ω) 0 ∂P) ≤
        B + c * (∫ ω in A, Occ ω ∂P) + ε := by
  classical
  intro ε hε K
  have hEventually : ∀ᶠ m : ℕ in atTop,
      (∫ ω in A, |N ω - M m ω| ∂P) < ε :=
    hL1.eventually (eventually_lt_nhds hε)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hEventually
  let m := max N₀ (K + 1)
  have hmK : K < m := by omega
  have hmErr : (∫ ω in A, |N ω - M m ω| ∂P) < ε :=
    hN₀ m (le_max_left _ _)
  refine ⟨m, hmK, ?_⟩
  have hBound : ∀ᵐ ω ∂(P.restrict A),
      max (F ω - M m ω) 0 ≤
        B + c * Occ ω + |N ω - M m ω| := by
    filter_upwards [hBudget, hOccNonneg] with ω hb ho
    have hupper : F ω - M m ω ≤
        B + c * Occ ω + |N ω - M m ω| := by
      have hdifference : N ω - M m ω ≤ |N ω - M m ω| :=
        le_abs_self _
      linarith
    apply max_le hupper
    nlinarith [mul_nonneg hc ho, abs_nonneg (N ω - M m ω)]
  have hConst : IntegrableOn (fun _ : Ω => B) A P := by
    exact integrable_const B
  have hTotal : IntegrableOn
      (fun ω => B + c * Occ ω + |N ω - M m ω|) A P :=
    (hConst.add (hOccI.const_mul c)).add (hErrI m)
  have hIntegral :=
    integral_mono_ae (hFI m) hTotal hBound
  have hSplit :
      (∫ ω in A, B + c * Occ ω + |N ω - M m ω| ∂P) =
      (∫ ω in A, B ∂P) +
      c * (∫ ω in A, Occ ω ∂P) +
      (∫ ω in A, |N ω - M m ω| ∂P) := by
    have hFirst :
        (∫ ω in A, B + c * Occ ω + |N ω - M m ω| ∂P) =
          (∫ ω in A, B + c * Occ ω ∂P) +
          (∫ ω in A, |N ω - M m ω| ∂P) := by
      simpa only [Pi.add_apply] using
        (integral_add (hConst.add (hOccI.const_mul c)) (hErrI m))
    have hSecond :
        (∫ ω in A, B + c * Occ ω ∂P) =
          (∫ ω in A, B ∂P) +
          (∫ ω in A, c * Occ ω ∂P) := by
      simpa only [Pi.add_apply] using
        (integral_add hConst (hOccI.const_mul c))
    rw [hFirst, hSecond]
    simp only [integral_const_mul]
  have hMeasure : (P A).toReal ≤ 1 := by
    have hPA : P A ≤ 1 := by
      calc
        P A ≤ P Set.univ := measure_mono (Set.subset_univ A)
        _ = 1 := measure_univ
    simpa using (ENNReal.toReal_mono (by norm_num) hPA)
  have hConstBound : (∫ ω in A, B ∂P) ≤ B := by
    have hm := mul_le_mul_of_nonneg_right hMeasure hB
    simpa [integral_const, Measure.restrict_apply_univ, smul_eq_mul, Measure.real] using hm
  rw [hSplit] at hIntegral
  linarith
