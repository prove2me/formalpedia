-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_uniform_compact_C1_negative_J_shift_commutator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:26:33.891777+00:00
-- url     : https://prove2.me/submissions/fcf93615-0819-4d6c-b663-bb6fe33c2fbf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Strict-compact C1 uniformity controls the original negative-J/Y mixed source commutator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ),
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
        let z : ℕ → ℝ := fun i =>
          x + X.X (u i) ω - rightLimit D (u i) ω
        let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
        let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
        (∀ i, i < n →
          Set.uIcc (z i - j i) (z i) ⊆ Set.Icc a b) →
        (∀ i, i < n →
          Set.uIcc (z i + c i - j i) (z i + c i) ⊆ Set.Icc a b) →
        (∀ i, i < n → |c i| < δ) →
        ∀ i, i < n →
          |w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)| ≤ ε * |j i| := by
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
  intro ω u n J Y z c j hBase hShift hSmall i hi
  let s : Set ℝ := Set.uIcc (z i - j i) (z i)
  let f : ℝ → ℝ := fun t => w (t + c i) - w t
  have htBand (t : ℝ) (ht : t ∈ s) : t ∈ Set.Icc a b :=
    hBase i hi ht
  have htShiftBand (t : ℝ) (ht : t ∈ s) :
      t + c i ∈ Set.Icc a b := by
    apply hShift i hi
    rcases Set.mem_uIcc.mp ht with h | h
    · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩)
    · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩)
  have hDiffShift (t : ℝ) (ht : t ∈ s) :
      DifferentiableAt ℝ (fun r : ℝ => w (r + c i)) t := by
    have hAdd : DifferentiableAt ℝ (fun r : ℝ => r + c i) t :=
      differentiableAt_id.add_const (c i)
    exact (hwDiff (t + c i) (htShiftBand t ht)).comp t hAdd
  have hDiffF (t : ℝ) (ht : t ∈ s) : DifferentiableAt ℝ f t :=
    (hDiffShift t ht).sub (hwDiff t (htBand t ht))
  have hDerivF (t : ℝ) (ht : t ∈ s) :
      deriv f t = deriv w (t + c i) - deriv w t := by
    change deriv ((fun r : ℝ => w (r + c i)) - w) t = _
    rw [deriv_sub (hDiffShift t ht) (hwDiff t (htBand t ht))]
    congr 1
    simpa [add_comm] using (deriv_comp_const_add w (c i) t)
  have hDerivBound (t : ℝ) (ht : t ∈ s) :
      ‖deriv f t‖ ≤ ε := by
    have hdist : dist (t + c i) t < δ := by
      simpa only [Real.dist_eq, add_sub_cancel_left] using hSmall i hi
    have hControlHere :=
      hControl (t + c i) (htShiftBand t ht) t (htBand t ht) hdist
    rw [hDerivF t ht]
    simpa only [Real.norm_eq_abs, Real.dist_eq] using le_of_lt hControlHere
  have hLip :=
    (convex_uIcc (z i - j i) (z i)).norm_image_sub_le_of_norm_deriv_le
      hDiffF hDerivBound Set.right_mem_uIcc Set.left_mem_uIcc
  have hRewrite :
      f (z i - j i) - f (z i) =
        w (z i + c i - j i) - w (z i + c i) -
          w (z i - j i) + w (z i) := by
    have hArg : z i - j i + c i = z i + c i - j i := by ring
    simp only [f, hArg]
    ring
  have hGap : ‖(z i - j i) - z i‖ = |j i| := by
    simp [Real.norm_eq_abs]
  have hGoal :
      |w (z i + c i - j i) - w (z i + c i) -
        w (z i - j i) + w (z i)| ≤ ε * |j i| := by
    calc
      |w (z i + c i - j i) - w (z i + c i) -
        w (z i - j i) + w (z i)| =
          ‖f (z i - j i) - f (z i)‖ := by rw [Real.norm_eq_abs, hRewrite]
      _ ≤ ε * ‖(z i - j i) - z i‖ := hLip
      _ = ε * |j i| := by rw [hGap]
  exact hGoal
