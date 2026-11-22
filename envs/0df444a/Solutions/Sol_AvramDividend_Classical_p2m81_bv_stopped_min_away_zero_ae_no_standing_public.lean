-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_stopped_min_away_zero_ae_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:08:15.297597+00:00
-- url     : https://prove2.me/submissions/401d9582-e191-498c-afdd-e4846cfc61c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_strict_lower_exit_no_creeping_ae_no_standing_public
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_clock_partition_of_finite
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ →
      x + X.X (min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω)).toNNReal ω ≠ 0 := by
  have hNoCreep : ∀ᵐ ω ∂P, twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω → x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0 := by
    simpa only [twoSidedExitDownTime, twoSidedExitUpTime] using p2m81_bv_strict_lower_exit_no_creeping_ae_no_standing_public X q φ hq hφ hroot W hW hBV a x ha hx0 hxa
  filter_upwards [hNoCreep] with ω hNC hmin
  have hPart := avram_root29_03_exit_clock_partition_of_finite X a x ha ω
  have hFin : twoSidedExitUpTime X (a - x) ω < ⊤ ∨ twoSidedExitDownTime X (-x) ω < ⊤ := min_lt_iff.mp hmin
  rcases hPart.mpr hFin with hUD | hDU
  · have hMinEq : min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) = twoSidedExitUpTime X (a - x) ω := min_eq_left (le_of_lt hUD)
    rw [hMinEq]; have hUfin : twoSidedExitUpTime X (a - x) ω < ⊤ := lt_of_lt_of_le hUD le_top
    have hUpGe : a - x ≤ X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω := by
      by_contra hlt; push_neg at hlt
      set U := (twoSidedExitUpTime X (a - x) ω).toNNReal with hU
      have hClock : twoSidedExitUpTime X (a - x) ω = ((U : ℝ≥0) : ℝ≥0∞) := by rw [hU]; exact (ENNReal.coe_toNNReal hUfin.ne).symm
      have hNe : twoSidedExitUpTime X (a - x) ω ≠ ⊤ := hUfin.ne
      have hT : twoSidedExitUpTime X (a - x) ω = ⨅ (t : ℝ≥0) (_ : (fun s : ℝ≥0 => a - x < X.X s ω) t), (t : ℝ≥0∞) := rfl
      have hBase := chat03_finite_extended_infimum_isGLB (fun s : ℝ≥0 => a - x < X.X s ω) (twoSidedExitUpTime X (a - x) ω) hT hNe
      have hToNN : (twoSidedExitUpTime X (a - x) ω).toNNReal = U := by rw [hClock]; exact ENNReal.toNNReal_coe U
      have hGLB : IsGLB {s : ℝ≥0 | a - x < X.X s ω} U := by rw [← hToNN]; exact hBase
      have hRight := X.rightCont ω U
      have hrr : ∀ᶠ s in 𝓝[Set.Ici U] U, (fun s : ℝ≥0 => X.X s ω) s < a - x := hRight.eventually (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hlt))
      have hmem : {s : ℝ≥0 | s ∈ Set.Ici U → (fun s : ℝ≥0 => X.X s ω) s < a - x} ∈ 𝓝 U := eventually_nhdsWithin_iff.mp hrr
      obtain ⟨u, hu, hsub⟩ := exists_Ico_subset_of_mem_nhds' hmem (lt_add_of_pos_right U zero_lt_one)
      have hb : u ∈ lowerBounds {s : ℝ≥0 | a - x < X.X s ω} := by intro s hs; by_contra hsu; have hts : U ≤ s := hGLB.1 hs; have hst : s < u := lt_of_not_ge hsu; exact (not_lt_of_ge (le_of_lt ((hsub ⟨hts, hst⟩) hts))) hs
      exact (not_le_of_gt hu.1) (hGLB.2 hb)
    have hpos : 0 < x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω := by linarith [hUpGe, ha]
    exact ne_of_gt hpos
  · have hMinEq : min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) = twoSidedExitDownTime X (-x) ω := min_eq_right (le_of_lt hDU)
    rw [hMinEq]; exact hNC hDU
