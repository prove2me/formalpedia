-- Prove2me | solution 1 for AvramDividend.Classical.avram_mixed_source13_original_annulus_uniform_grid_factorial_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:20:10.691436+00:00
-- url     : https://prove2.me/submissions/897e203f-6059-48b7-8643-1d5fde25b035

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_factorial_integrable
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_grid_real_sum
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_equal_mesh_triangular_rate_real
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_window_count_finset_filter
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_factorial_moment_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus14_original_pathwise_grid_factorial_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- Original physical annulus uniform-grid factorial expectation bounds. UNFINISHED LOCAL DRAFT: source is not uploadable while the marked goals remain. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 T ×ˢ B)
    let rB : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    let rM : ℝ := ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((m : ℝ) + 1))))).toReal
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧ ∀ k : ℕ,
        let q : ℝ := ((k + 1 : ℕ) : ℝ)
        rB ^ 2 * (1 - 1 / q) ≤ (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) ∧
        (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) ≤ rB ^ 2 * (1 - 1 / q) + rM ^ 2 / q := by
  classical
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 T ×ˢ B)
  let rB : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  let rM : ℝ := ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((m : ℝ) + 1))))).toReal
  let Y : Ω → ℝ := fun ω => (N ω).toReal * ((N ω).toReal - 1)
  change Integrable Y P ∧ ∀ k : ℕ,
      let q : ℝ := ((k + 1 : ℕ) : ℝ)
      rB ^ 2 * (1 - 1 / q) ≤ (∫ ω, Y ω ∂P) ∧
      (∫ ω, Y ω ∂P) ≤ rB ^ 2 * (1 - 1 / q) + rM ^ 2 / q
  have hYInt : Integrable Y P := by
    simpa [Y, N, B] using (avram_mix_fin_source13_original_annulus_factorial_integrable X T n m hnm)
  refine ⟨hYInt, ?_⟩
  intro k
  let q : ℕ := k + 1
  let δ : ℝ≥0 := T / (q : ℝ≥0)
  let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
  have hq : 0 < q := Nat.succ_pos k
  have hZero : grid 0 = 0 := by simp [grid]
  have hStep : ∀ i, grid i ≤ grid (i + 1) := by intro i; dsimp [grid]; gcongr; omega
  have hT : grid q = T := by
    dsimp [grid, δ]
    have hne : (q : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    field_simp
  let F : Ω → Finset ℝ≥0 := fun ω => (avram_wave7_06_original_negative_band_marked_times_finite X ω T m).toFinset
  let a : ℕ → Ω → ℕ := fun i ω => ((F ω).filter (fun u => grid i < u ∧ u ≤ grid (i + 1) ∧
      -(1 / ((n : ℝ) + 1)) < X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)).card
  let b : ℕ → Ω → ℕ := fun i ω => ((F ω).filter (fun u => grid i < u ∧ u ≤ grid (i + 1))).card
  let H : Ω → ℝ := fun ω => 2 * (∑ i ∈ Finset.range q, (∑ j ∈ Finset.range i, (a j ω : ℝ)) * (a i ω : ℝ))
  let D : Ω → ℝ := fun ω => ∑ i ∈ Finset.range q, (b i ω : ℝ) * ((b i ω : ℝ) - 1)
  let J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun s t ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B)
  have hMono : Monotone grid := monotone_nat_of_le_succ hStep
  have hEnd (i : ℕ) (hi : i < q) : grid (i + 1) ≤ T := by rw [← hT]; exact hMono (Nat.succ_le_of_lt hi)
  have hCell (i : ℕ) (hi : i < q) (ω : Ω) : J (grid i) (grid (i + 1)) ω = (a i ω : ℝ≥0∞) := by exact avram_mix_annulus14_original_window_filter_card X ω (grid i) (grid (i + 1)) T (hStep i) (hEnd i hi) n m hnm
  have hA (i : ℕ) (hi : i < q) (ω : Ω) : (J (grid i) (grid (i + 1)) ω).toReal = (a i ω : ℝ) := by rw [hCell i hi ω, ENNReal.toReal_natCast]
  have hPrefix (i : ℕ) (hi : i ≤ q) (ω : Ω) :
      (J 0 (grid i) ω).toReal = ∑ j ∈ Finset.range i, (a j ω : ℝ) := by
    have hTel := avram_p4_s3_run1640_original_marked_count_grid_telescoping X ω grid hStep hZero B measurableSet_Ioc i
    change (∑ j ∈ Finset.range i, J (grid j) (grid (j + 1)) ω) = J 0 (grid i) ω at hTel
    have hSum :
        (∑ j ∈ Finset.range i, (a j ω : ℝ≥0∞)) = J 0 (grid i) ω := by
      calc
        _ = ∑ j ∈ Finset.range i, J (grid j) (grid (j + 1)) ω := by
          exact Finset.sum_congr rfl (fun j hj => by
            have hjq : j < q := lt_of_lt_of_le (Finset.mem_range.mp hj) hi
            exact (hCell j hjq ω).symm)
        _ = J 0 (grid i) ω := hTel
    have hReal := congrArg ENNReal.toReal hSum.symm
    change (J 0 (grid i) ω).toReal = (∑ j ∈ Finset.range i, (a j ω : ℝ≥0∞)).toReal at hReal
    have hRealCast :
        (∑ j ∈ Finset.range i, (a j ω : ℝ≥0∞)).toReal = ∑ j ∈ Finset.range i, (a j ω : ℝ) := by
      simpa only [ENNReal.toReal_natCast] using (ENNReal.toReal_sum (s := Finset.range i) (f := fun j : ℕ => (a j ω : ℝ≥0∞)) (by intro j hj; simp))
    exact hReal.trans hRealCast
  have hCross (ω : Ω) : H ω = 2 * (∑ i ∈ Finset.range q, (J 0 (grid i) ω).toReal * (J (grid i) (grid (i + 1)) ω).toReal) := by dsimp [H]; congr 1; apply Finset.sum_congr rfl; intro i hi; rw [hPrefix i (Nat.le_of_lt (Finset.mem_range.mp hi)) ω, hA i (Finset.mem_range.mp hi) ω]
  have hPath (ω : Ω) : H ω ≤ Y ω ∧ Y ω ≤ H ω + D ω := by
    have h := avram_mix_annulus14_original_pathwise_grid_factorial_sandwich X ω T n m hnm grid hStep hZero q hT
    change H ω ≤ Y ω ∧ Y ω ≤ H ω + D ω at h; exact h
  -- Four remaining expectation bridges; each must use original J counts.
  have hHInt : Integrable H P := by
    have h := (avram_mix_fin_source13_original_annulus_grid_real_sum X grid hStep q n m hnm).1
    change Integrable (fun ω => ∑ i ∈ Finset.range q, (J 0 (grid i) ω).toReal * (J (grid i) (grid (i + 1)) ω).toReal) P at h
    have h2 := h.const_mul (2 : ℝ)
    exact h2.congr (Filter.Eventually.of_forall (fun ω => (hCross ω).symm))
  have hCellLen (i : ℕ) : grid (i + 1) - grid i = δ := by dsimp [grid]; rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]; exact add_tsub_cancel_left _ _
  have hRealT : rB = (T : ℝ) * (X.ν B).toReal := by simp [rB, ENNReal.toReal_mul]
  have hRatePrefix (i : ℕ) : (((grid i : ℝ≥0∞) * X.ν B).toReal) = (((i : ℝ) * (T : ℝ)) / (q : ℝ)) * (X.ν B).toReal := by simp [grid, δ, ENNReal.toReal_mul] <;> ring <;> simp
  have hRateCell (i : ℕ) : ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) = (((((i : ℝ) + 1) * (T : ℝ)) / (q : ℝ) - ((i : ℝ) * (T : ℝ)) / (q : ℝ)) * (X.ν B).toReal) := by rw [hCellLen]; simp [δ, ENNReal.toReal_mul] <;> ring <;> simp
  have hHMean : (∫ ω, H ω ∂P) = rB ^ 2 * (1 - 1 / (q : ℝ)) := by
    have hRaw := (avram_mix_fin_source13_original_annulus_grid_real_sum X grid hStep q n m hnm).2
    change (∫ ω, (∑ i ∈ Finset.range q, (J 0 (grid i) ω).toReal * (J (grid i) (grid (i + 1)) ω).toReal) ∂P) = ∑ i ∈ Finset.range q, (((grid i : ℝ≥0∞) * X.ν B).toReal) * ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) at hRaw
    calc
      (∫ ω, H ω ∂P) = 2 * (∫ ω, (∑ i ∈ Finset.range q, (J 0 (grid i) ω).toReal * (J (grid i) (grid (i + 1)) ω).toReal) ∂P) := by
                simp_rw [hCross]
                rw [integral_const_mul]
      _ = 2 * (∑ i ∈ Finset.range q, (((grid i : ℝ≥0∞) * X.ν B).toReal) * ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) := by rw [hRaw]
      _ = 2 * (∑ i ∈ Finset.range q, ((((i : ℝ) * (T : ℝ)) / (q : ℝ)) * (X.ν B).toReal) * (((((i : ℝ) + 1) * (T : ℝ)) / (q : ℝ) - ((i : ℝ) * (T : ℝ)) / (q : ℝ)) * (X.ν B).toReal)) := by
                congr 1
                apply Finset.sum_congr rfl
                intro i hi
                rw [hRatePrefix, hRateCell]
      _ = rB ^ 2 * (1 - 1 / (q : ℝ)) := by
        rw [avram_leanlevy_bridge_original_equal_mesh_triangular_rate_real (T : ℝ) (X.ν B).toReal q, hRealT]
        have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
        field_simp <;> ring
  have hGridAdd (i : ℕ) : grid (i + 1) = grid i + δ := by dsimp [grid]; rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  let M : Set ℝ := Iic (-(1 / ((m : ℝ) + 1)))
  let K : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun s t ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ M)
  have hFullCell (i : ℕ) (hi : i < q) (ω : Ω) : K (grid i) (grid (i + 1)) ω = (b i ω : ℝ≥0∞) := by exact avram_p2_e_compensator_original_window_count_finset_filter X ω (grid i) (grid (i + 1)) T (hStep i) (hEnd i hi) m
  have hFullMoment (i : ℕ) (hi : i < q) :
      Integrable (fun ω => (b i ω : ℝ) * ((b i ω : ℝ) - 1)) P ∧
      (∫ ω, (b i ω : ℝ) * ((b i ω : ℝ) - 1) ∂P) = (((δ : ℝ≥0∞) * X.ν M).toReal) ^ 2 := by
    have hF := avram_p4_s3_interval_h_original_full_cutoff_shifted_factorial_moment_exact X (grid i) δ m
    change Integrable (fun ω => (K (grid i) (grid i + δ) ω).toReal * ((K (grid i) (grid i + δ) ω).toReal - 1)) P ∧ (∫ ω, (K (grid i) (grid i + δ) ω).toReal * ((K (grid i) (grid i + δ) ω).toReal - 1) ∂P) = (((δ : ℝ≥0∞) * X.ν M).toReal) ^ 2 at hF
    have hCellEq (ω : Ω) : (K (grid i) (grid i + δ) ω).toReal = (b i ω : ℝ) := by rw [← hGridAdd, hFullCell i hi ω, ENNReal.toReal_natCast]
    simpa only [hCellEq] using hF
  have hDInt : Integrable D P := by
    have h := integrable_finset_sum (Finset.range q) (fun i hi => (hFullMoment i (Finset.mem_range.mp hi)).1)
    simpa only [D, Finset.sum_apply] using h
  have hDMean : (∫ ω, D ω ∂P) = rM ^ 2 / (q : ℝ) := by
    have hCellMean :
        (∫ ω, D ω ∂P) = (q : ℝ) * (((δ : ℝ≥0∞) * X.ν M).toReal) ^ 2 := by
      dsimp [D]
      rw [integral_finset_sum (Finset.range q) (fun i hi => (hFullMoment i (Finset.mem_range.mp hi)).1)]
      have hconst : (∑ i ∈ Finset.range q, ∫ ω, (b i ω : ℝ) * ((b i ω : ℝ) - 1) ∂P) = ∑ i ∈ Finset.range q, (((δ : ℝ≥0∞) * X.ν M).toReal) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hFullMoment i (Finset.mem_range.mp hi)).2
      rw [hconst]
      simp
    have hRate : (((δ : ℝ≥0∞) * X.ν M).toReal) = rM / (q : ℝ) := by simp [rM, M, δ, ENNReal.toReal_mul] <;> ring
    rw [hCellMean, hRate]
    have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
    field_simp <;> ring
  constructor
  · calc
      rB ^ 2 * (1 - 1 / (q : ℝ)) = (∫ ω, H ω ∂P) := hHMean.symm
      _ ≤ (∫ ω, Y ω ∂P) := integral_mono hHInt hYInt (fun ω => (hPath ω).1)
  · calc
      (∫ ω, Y ω ∂P) ≤ (∫ ω, H ω + D ω ∂P) := integral_mono hYInt (hHInt.add hDInt) (fun ω => (hPath ω).2)
      _ = (∫ ω, H ω ∂P) + (∫ ω, D ω ∂P) := integral_add hHInt hDInt
      _ = rB ^ 2 * (1 - 1 / (q : ℝ)) + rM ^ 2 / (q : ℝ) := by
        rw [hHMean, hDMean]