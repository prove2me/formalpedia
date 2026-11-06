-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_clipped_finite_prefix_arbitrary_weights_positive_lintegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:51:44.576228+00:00
-- url     : https://prove2.me/submissions/d7486457-6a6b-4409-9b7b-d8464aab3d9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_arbitrary_nonnegative_weights_positive_lintegral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Arbitrary random nonnegative weights preserve zero positive outer mass for
the true nonlinear BV reserve correction when only the used finite prefix is
monotone. No assumption is made on the future grid tail or signed R-L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (τ : Ω → ℝ≥0) (u : Ω → ℕ → ℝ≥0)
    (n : Ω → ℕ) (a : Ω → ℕ → ℝ)
    (hu : ∀ ω i, i < n ω → u ω i ≤ u ω (i + 1))
    (ha : ∀ ω i, 0 ≤ a ω i) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let G : Ω → ℝ := fun ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u ω i) (τ ω)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      ∑ i : Fin (n ω),
        a ω i *
          (V (riskProcess X x D (v i) ω -
            (R (v (i + 1)) - R (v i))) -
           V (riskProcess X x D (v i) ω))
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) = 0 := by
  let u' : Ω → ℕ → ℝ≥0 := fun ω j => u ω (min j (n ω))
  have hu' : ∀ ω, Monotone (u' ω) := by
    intro ω
    apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < n ω
    · simpa [u', Nat.min_eq_left (Nat.le_of_lt hi),
        Nat.min_eq_left (Nat.succ_le_of_lt hi)] using hu ω i hi
    · have hni : n ω ≤ i := Nat.le_of_not_gt hi
      simp [u', Nat.min_eq_right hni,
        Nat.min_eq_right (hni.trans (Nat.le_succ i))]
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  let G : Ω → ℝ := fun ω =>
    let v : ℕ → ℝ≥0 := fun i => min (u ω i) (τ ω)
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
          else 0).toReal
    ∑ i : Fin (n ω),
      a ω i *
        (V (riskProcess X x D (v i) ω -
          (R (v (i + 1)) - R (v i))) -
         V (riskProcess X x D (v i) ω))
  let G' : Ω → ℝ := fun ω =>
    let v : ℕ → ℝ≥0 := fun i => min (u' ω i) (τ ω)
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
          else 0).toReal
    ∑ i : Fin (n ω),
      a ω i *
        (V (riskProcess X x D (v i) ω -
          (R (v (i + 1)) - R (v i))) -
         V (riskProcess X x D (v i) ω))
  have heq (ω : Ω) : G ω = G' ω := by
    dsimp [G, G', u']
    apply Finset.sum_congr rfl
    intro i _
    have h0 : min (i : ℕ) (n ω) = (i : ℕ) :=
      Nat.min_eq_left (Nat.le_of_lt i.isLt)
    have h1 : min ((i : ℕ) + 1) (n ω) = ((i : ℕ) + 1) :=
      Nat.min_eq_left (Nat.succ_le_of_lt i.isLt)
    simp [h0, h1]
  have h := avram_p3_2_original_clipped_arbitrary_nonnegative_weights_positive_lintegral_zero
    X hBV x D w C hC hw_cont hw0 hw_neg hw_smooth hw_grad τ u' hu' n a ha
  dsimp only at h ⊢
  change (∫⁻ ω, ENNReal.ofReal (G' ω) ∂P) = 0 at h
  calc
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) =
        (∫⁻ ω, ENNReal.ofReal (G' ω) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact congrArg ENNReal.ofReal (heq ω)
    _ = 0 := h
