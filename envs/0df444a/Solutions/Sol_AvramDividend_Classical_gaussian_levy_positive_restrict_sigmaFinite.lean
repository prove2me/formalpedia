-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_positive_restrict_sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:26:55.816241+00:00
-- url     : https://prove2.me/submissions/ede59b64-8368-45c6-a51d-9d92e27a6fa1

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_positive_tail_finite
import Theorems.Thm_AvramDividend_Classical_gaussian_positive_reciprocal_tail_cover

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The positive part of a truncated-square Lévy measure is sigma-finite. -/
theorem solution (μ : Measure ℝ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    SigmaFinite (μ.restrict (Ioi (0 : ℝ))) := by
  let ν : Measure ℝ := μ.restrict (Ioi 0)
  let spans : ℕ → Set ℝ := fun n =>
    if n = 0 then Iic (0 : ℝ) else Ici ((n : ℝ)⁻¹)
  have hzero : ν (Iic (0 : ℝ)) = 0 := by
    change (μ.restrict (Ioi 0)) (Iic 0) = 0
    rw [Measure.restrict_apply measurableSet_Iic]
    have he : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
      ext x
      constructor
      · intro hx
        exact (not_lt_of_ge (show x ≤ 0 from hx.1))
          (show 0 < x from hx.2)
      · intro hx
        exact False.elim hx
    simp [he]
  have hfinite : ∀ n, ν (spans n) < ⊤ := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [spans, hzero]
    · have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hcut : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
      have htail :=
        AvramDividend.Classical.gaussian_levy_positive_tail_finite
          μ ((n : ℝ)⁻¹) hcut hlevy
      have hbound : ν (Ici ((n : ℝ)⁻¹)) ≤ μ (Ici ((n : ℝ)⁻¹)) := by
        change (μ.restrict (Ioi 0)) (Ici ((n : ℝ)⁻¹)) ≤ _
        rw [Measure.restrict_apply measurableSet_Ici]
        exact measure_mono Set.inter_subset_left
      have hfin := lt_of_le_of_lt hbound htail
      simpa [spans, hn] using hfin
  have hspan : (⋃ n, spans n) = Set.univ := by
    exact AvramDividend.Classical.gaussian_positive_reciprocal_tail_cover
  exact sigmaFinite_iff.mpr ⟨{
    set := spans
    set_mem := fun n => Set.mem_univ _
    finite := hfinite
    spanning := hspan
  }⟩
