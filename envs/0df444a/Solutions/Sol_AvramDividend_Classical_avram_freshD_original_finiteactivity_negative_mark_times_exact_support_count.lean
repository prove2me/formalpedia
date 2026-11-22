-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_finiteactivity_negative_mark_times_exact_support_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:47:24.264899+00:00
-- url     : https://prove2.me/submissions/7275820d-8fe0-4486-94cb-87991b58f831

/-
  Finite-activity physical jump support: construct the exact finite set
  from the proved pathwise finiteness statement, then identify the count
  with the original marked jump measure.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_marked_times_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    ∃ S : Ω → Finset ℝ≥0,
      ∀ᵐ ω ∂P,
        (∀ u : ℝ≥0, u ∈ S ω ↔
          0 < u ∧ u ≤ T ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0) ∧
        ((S ω).card : ℝ) =
          (((Measure.count.restrict {u : ℝ≥0 |
             0 < u ∧ X.X u ω -
               Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 =>
                (u, X.X u ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal := by
  classical
  let A : Ω → Set ℝ≥0 := fun ω =>
    {u | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0}
  have hA : ∀ᵐ ω ∂P, (A ω).Finite := by
    simpa only [A, Set.mem_Iio] using
      (avram_a20_original_borel_physical_marked_times_finite_ae
        X hFinite T (Iio (0 : ℝ)) measurableSet_Iio Subset.rfl)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    if h : (A ω).Finite then h.toFinset else ∅
  refine ⟨S, ?_⟩
  filter_upwards [hA] with ω hfin
  have hS : ∀ u : ℝ≥0, u ∈ S ω ↔
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 := by
    intro u
    have hm : u ∈ S ω ↔ u ∈ A ω := by simp [S, hfin]
    simpa only [A, Set.mem_setOf_eq] using hm
  have hFilter : (S ω).filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ T) = S ω := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact ⟨((hS u).mp hu).1, ((hS u).mp hu).2.1⟩
  have hCount :=
    avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
      X ω T (Iio (0 : ℝ)) measurableSet_Iio (S ω)
      (by intro u; simpa only [Set.mem_Iio] using hS u)
      0 T (by exact zero_le) le_rfl
  refine ⟨hS, ?_⟩
  have hc := congrArg ENNReal.toReal hCount
  simpa [hFilter] using hc.symm
