-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys89b_original_zero_contact_drift_only_budget_type0_is_false
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:42:15.063036+00:00
-- url     : https://prove2.me/submissions/e90a55a6-cd91-4dff-8a71-08b48cfc32a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_BVZeroContactUniversalClaimType0
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_strict_uniform_grid_HJB_B_nonpos_and_prepayment_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_nojump_unitdrift_path_satisfies_all_phys89b_contact_antecedents
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_positive_event_conditional_ae_convergence_contradicts_pointwise_failure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

private theorem bvb_type0_core :
    ¬ BVZeroContactUniversalClaimType0 := by
  intro hUniversal
  obtain ⟨P, 𝓕, X, hStanding, hBV, hNu, hActivity, hDrift, hSigma,
    hPositive, hHyp⟩ :=
    AvramDividend.Classical.avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness
  let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
  let D := barrierStrategy X 0 0
  let C : ℝ≥0∞ := 1
  rcases hHyp with ⟨hwCont, hw0, hwNeg, hwSmooth, hwGen, hwGrad,
    hAdmissible, hwNonneg, hJump⟩
  let T : ℝ := 1 / 10
  have hT : 0 < T := by norm_num [T]
  let u : ℕ → ℕ → ℝ≥0 := fun n i =>
    ⟨T * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
  have hUniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2) := by
    intro n i; rfl
  have hMonoAll : ∀ n i, u n i ≤ u n (i + 1) := by
    intro n i
    change T * (i : ℝ) / ((n : ℝ) + 2) ≤
      T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)
    gcongr
    all_goals omega
  have hMono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1) := by
    intro n i _; exact hMonoAll n i
  have hGrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)) := by
    intro n
    constructor
    · apply Subtype.ext
      simp [u]
    · change T * ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) =
        T - T / ((n : ℝ) + 2)
      norm_num [T]
      push_cast
      have hn : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
  let B : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω => let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => 0 + X.X t ω - rightLimit D t ω) (u n i); (∑ i ∈ Finset.range (n + 1), if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then Real.exp (-(1 * (u n i : ℝ))) * (X.generator w (Z i) - 1 * w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) + (let J : ℝ≥0 → ℝ := fun t => ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0; let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t; ∑ i ∈ Finset.range (n + 1), (if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then Real.exp (-(1 * (u n i : ℝ))) * deriv w (Z i) else 0) * (R (u n i) - R (u n (i + 1))))
  have hwGen1 : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - 1 * w y ≤ 0 := by
    intro y hy hc
    simpa only [one_mul] using hwGen y hy hc
  have hDstrategy : IsDividendStrategy 𝓕 D := hAdmissible.1.1
  have hAux :=
    AvramDividend.Classical.avram_bvb_original_strict_uniform_grid_HJB_B_nonpos_and_prepayment_ae
      X hStanding hBV (1 : ℝ) w C hwGen1 0 D u hMonoAll hDstrategy
      T hT hUniform
  have hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0 := hAux.1
  have hPre : ∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) = riskProcess X 0 D (u n (i + 1)) ω := hAux.2
  have hAe := hUniversal X hStanding hBV (1 : ℝ) (by norm_num)
    w C (by norm_num [C]) hwCont hw0 hwNeg hwSmooth hwGen1 hwGrad
    (0 : ℝ) (by norm_num) (by norm_num [C])
    D hAdmissible hwNonneg hJump T hT u hGrid hMono hUniform
    B (by intro n omega; rfl) hAllB hPre (by norm_num [C]) hActivity
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  have hS : S = (1 / 10 : NNReal) := by
    apply Subtype.ext
    norm_num [S, T]
  let F : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω => (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iio (T - δ n), ENNReal.ofReal (Real.exp (-(1 * t))) ∂(dividendMeasure D ω)).toReal + (if (S : ℝ≥0∞) < ruinTime X 0 D ω then Real.exp (-(1 * T)) * w (riskProcess X 0 D S ω) else 0)
  let L : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω => let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => 0 + X.X t ω - rightLimit D t ω) (u n i); ∑ i ∈ Finset.range (n + 1), if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then Real.exp (-(1 * (u n i : ℝ))) * (X.drift * deriv w (Z i) - 1 * w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0
  let A : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun n ω => F n ω - (w 0 + L n ω)
  let τ : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ≥0∞ :=
    fun ω => ruinTime X 0 D ω
  let E : Set ((ℕ → ℝ) × (ℕ → ℝ)) := {ω | ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ∧ (∀ t : ℝ≥0, t ≤ 1 → X.X t ω = (t : ℝ) * X.drift)}
  have hSurvive : ∀ ω ∈ E, τ ω ≠ 0 := by
    intro ω hω
    have hFacts :=
      AvramDividend.Classical.avram_bvb_original_nojump_unitdrift_path_satisfies_all_phys89b_contact_antecedents
        X ω hDrift hω.2 hω.1
    exact ne_of_gt (lt_of_le_of_lt (by exact bot_le) hFacts.2.2.1)
  have hFails : ∀ ω ∈ E,
      ¬ Tendsto (fun n => max (A n ω) 0) atTop (𝓝 (0 : ℝ)) := by
    intro ω hω
    simpa only [A, F, L, δ, T, u, w, D, hS, one_mul] using
      (AvramDividend.Classical.avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
        X ω hDrift hω.2)
  have hAeE : ∀ᵐ ω ∂P, ω ∈ E →
      Tendsto (fun n => if τ ω = 0 then 0 else max (A n ω) 0)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hAe] with ω hω
    intro hE
    have hFacts :=
      AvramDividend.Classical.avram_bvb_original_nojump_unitdrift_path_satisfies_all_phys89b_contact_antecedents
        X ω hDrift hE.2 hE.1
    exact hω hFacts.1 hFacts.2.1 hFacts.2.2.1 hFacts.2.2.2
  exact AvramDividend.Classical.avram_bvb_original_positive_event_conditional_ae_convergence_contradicts_pointwise_failure
    P E τ A hPositive hSurvive hFails hAeE

theorem solution : ¬ BVZeroContactUniversalClaimType0 := bvb_type0_core
