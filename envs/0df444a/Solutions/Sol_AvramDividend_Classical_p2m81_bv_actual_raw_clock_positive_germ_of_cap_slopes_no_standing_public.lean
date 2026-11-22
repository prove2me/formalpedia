-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_actual_raw_clock_positive_germ_of_cap_slopes_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T09:47:12.223651+00:00
-- url     : https://prove2.me/submissions/36ebf0db-02be-453b-8113-23f4647ecdc4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_dyadic_slope_to_positive_right_germ_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_countable_cap_germs_to_finite_raw_clock_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_le_drift_mul
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_eventual_psi_above_no_standing_public
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation)
    (τ : Ω → ℝ≥0∞) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hCapSlope : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal + δ n) ω -
            X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω)) /
          (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      τ ω < ⊤ →
      ∃ ε : ℝ≥0, 0 < ε ∧
        ∀ t : ℝ≥0, 0 < t → t < ε →
          0 < X.X ((τ ω).toNNReal + t) ω -
            X.X ((τ ω).toNNReal) ω := by
  obtain ⟨β₀, _, hEvent⟩ :=
    p2m81_bv_root_eventual_psi_above_no_standing_public X q φ hq hφ hroot hBV
  set θ : ℝ := max β₀ 1 with hθdef
  have hθ1 : 1 ≤ θ := le_max_right _ _
  have hβθ : β₀ ≤ θ := le_max_left _ _
  have hqψ : q < X.ψ θ := hEvent θ hβθ
  have hle : X.ψ θ ≤ X.drift * θ :=
    bv_laplace_exponent_le_drift_mul X hBV θ hθ1
  have hθpos : 0 < θ := lt_of_lt_of_le zero_lt_one hθ1
  have hpos : 0 < X.drift * θ := lt_of_lt_of_le (lt_trans hq hqψ) hle
  have hd : 0 < X.drift := by
    by_contra h
    push_neg at h
    have hle0 : X.drift * θ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (le_of_lt hθpos)
    linarith
  let G : ℝ≥0 → Ω → Prop := fun s ω =>
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, 0 < t → t < ε →
        0 < X.X (s + t) ω - X.X s ω
  have hCapGerms : ∀ N : ℕ, ∀ᵐ ω ∂P,
      G ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω := by
    intro N
    filter_upwards [bv_drift_deficit_ae_monotone_all_times X hBV,
      hCapSlope N] with ω hMon hSlopeω
    let S₀ : ℝ≥0 → ℝ :=
      fun s => X.drift * (s : ℝ) - X.X s ω
    let S : ℝ≥0 → ℝ := fun t =>
      S₀ ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal + t) -
        S₀ ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal)
    have hSmon : Monotone S := by
      intro t u htu
      let c : ℝ≥0 := (τ ω ⊓ (N : ℝ≥0∞)).toNNReal
      have hshift : c + t ≤ c + u := add_le_add (le_refl c) htu
      change S₀ (c + t) - S₀ c ≤ S₀ (c + u) - S₀ c
      exact sub_le_sub_right (hMon hshift) (S₀ c)
    have hIdentity (t : ℝ≥0) :
        S t = X.drift * (t : ℝ) -
          (X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal + t) ω -
            X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω) := by
      dsimp [S, S₀]
      ring
    have hSlopeS :
        Tendsto (fun n : ℕ => S (δ n) / (δ n : ℝ))
          atTop (𝓝 (0 : ℝ)) := by
      have hEq :
          (fun n : ℕ => S (δ n) / (δ n : ℝ)) =
          (fun n : ℕ =>
            (X.drift * (δ n : ℝ) -
              (X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal + δ n) ω -
                X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω)) /
                (δ n : ℝ)) := by
        funext n
        rw [hIdentity]
      rw [hEq]
      exact hSlopeω
    obtain ⟨ε, hεpos, hε⟩ :=
      bv_dyadic_slope_to_positive_right_germ_ws01c
        S δ X.drift hd hδpos hSmon hRatio hCover hSlopeS
    show ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, 0 < t → t < ε →
        0 < X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal + t) ω -
          X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω
    refine ⟨ε, hεpos, ?_⟩
    intro t ht hte
    have hPositive := hε t ht hte
    rw [hIdentity] at hPositive
    convert hPositive using 1 <;> ring
  exact bv_countable_cap_germs_to_finite_raw_clock_ws01c
    P τ G hCapGerms
