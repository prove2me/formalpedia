-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_raw_J_commutator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:25:38.545251+00:00
-- url     : https://prove2.me/submissions/1764282f-e6e2-4b0a-b405-c5f4a6b16e3f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A uniform compact C1 modulus controls arbitrary physical drift shifts
against the actual raw-J jump segments, including cap-safe interior cells. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z c j : ℝ,
        Set.uIcc (z - j) z ⊆ Set.Icc a b →
        Set.uIcc (z + c - j) (z + c) ⊆ Set.Icc a b →
        |c| < δ →
        |w (z + c - j) - w (z + c) -
          w (z - j) + w z| ≤ ε * |j| := by
  have hCont : ContinuousOn (deriv w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hwC1.continuousOn_deriv_of_isOpen hOpen (by norm_num)
  have hUnif : UniformContinuousOn (deriv w) (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hCont.mono hBand)
  have hDiffOn : DifferentiableOn ℝ w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hwC1.differentiableOn (by norm_num)
  have hwDiff (t : ℝ) (ht : t ∈ Set.Icc a b) :
      DifferentiableAt ℝ w t :=
    hDiffOn.differentiableAt (hOpen.mem_nhds (hBand ht))
  intro ε hε
  obtain ⟨δ, hδ, hControl⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUnif) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z c j hBase hShift hSmall
  let s : Set ℝ := Set.uIcc (z - j) z
  let f : ℝ → ℝ := fun t => w (t + c) - w t
  have htBand (t : ℝ) (ht : t ∈ s) : t ∈ Set.Icc a b :=
    hBase ht
  have htShiftBand (t : ℝ) (ht : t ∈ s) :
      t + c ∈ Set.Icc a b := by
    apply hShift
    rcases Set.mem_uIcc.mp ht with h | h
    · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩)
    · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩)
  have hDiffShift (t : ℝ) (ht : t ∈ s) :
      DifferentiableAt ℝ (fun r : ℝ => w (r + c)) t := by
    have hAdd : DifferentiableAt ℝ (fun r : ℝ => r + c) t :=
      differentiableAt_id.add_const c
    exact (hwDiff (t + c) (htShiftBand t ht)).comp t hAdd
  have hDiffF (t : ℝ) (ht : t ∈ s) : DifferentiableAt ℝ f t :=
    (hDiffShift t ht).sub (hwDiff t (htBand t ht))
  have hDerivF (t : ℝ) (ht : t ∈ s) :
      deriv f t = deriv w (t + c) - deriv w t := by
    change deriv ((fun r : ℝ => w (r + c)) - w) t = _
    rw [deriv_sub (hDiffShift t ht) (hwDiff t (htBand t ht))]
    congr 1
    simpa [add_comm] using (deriv_comp_const_add w c t)
  have hDerivBound (t : ℝ) (ht : t ∈ s) :
      ‖deriv f t‖ ≤ ε := by
    have hdist : dist (t + c) t < δ := by
      simpa only [Real.dist_eq, add_sub_cancel_left] using hSmall
    have hControlHere :=
      hControl (t + c) (htShiftBand t ht) t (htBand t ht) hdist
    rw [hDerivF t ht]
    simpa only [Real.norm_eq_abs, Real.dist_eq] using le_of_lt hControlHere
  have hLip :=
    (convex_uIcc (z - j) z).norm_image_sub_le_of_norm_deriv_le
      hDiffF hDerivBound Set.right_mem_uIcc Set.left_mem_uIcc
  have hRewrite :
      f (z - j) - f z =
        w (z + c - j) - w (z + c) - w (z - j) + w z := by
    have hArg : z - j + c = z + c - j := by ring
    simp only [f, hArg]
    ring
  have hGap : ‖(z - j) - z‖ = |j| := by
    simp [Real.norm_eq_abs]
  calc
    |w (z + c - j) - w (z + c) - w (z - j) + w z| =
        ‖f (z - j) - f z‖ := by rw [Real.norm_eq_abs, hRewrite]
    _ ≤ ε * ‖(z - j) - z‖ := hLip
    _ = ε * |j| := by rw [hGap]
