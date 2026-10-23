-- Prove2me | solution 1 for AvramDividend.Classical.chat03_capped_actual_scale_expectation_identity_from_continuous_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:22:00.29539+00:00
-- url     : https://prove2.me/submissions/85a5acea-f8ff-4ac9-93ca-656bf0b491fa

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_capped_actual_scale_expectation_identity_of_sampled_martingale
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

/-!
Continuous-time martingales admit the sampled martingale and reserve
adaptation hypotheses of the finite-horizon two-sided exit identity.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (lower upper : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P, IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (mesh : ℕ → ℝ≥0) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    (clock : ℕ → ℕ → ℝ≥0)
    (hclock : ∀ n k, clock n k = min ((k : ℝ≥0) * mesh n) T)
    (hAdapt : Adapted 𝓕 X.X)
    (hMart : Martingale
      (fun (t : ℝ≥0) ω => Real.exp (-(q * (t : ℝ))) *
        W (x + X.X t ω)) 𝓕 P)
    (hInit : ∀ n, (∫ ω,
      Real.exp (-(q * (clock n 0 : ℝ))) *
        W (x + X.X (clock n 0) ω) ∂P) = W x) :
    (∫ ω, Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
      W (x + X.X (min (τ ω) T) ω) ∂P) = W x := by
  have hMon (n : ℕ) : Monotone (clock n) := by
    intro i j hij
    rw [hclock n i, hclock n j]
    have hc : (i : ℝ≥0) ≤ j := by exact_mod_cast hij
    exact min_le_min_right T
      (mul_le_mul_of_nonneg_right hc (le_of_lt (hpos n)))
  let H (n : ℕ) : Filtration ℕ mΩ :=
    { seq := fun k => 𝓕 (clock n k)
      mono' := fun _ _ hij => 𝓕.mono (hMon n hij)
      le' := fun _ => 𝓕.le _ }
  have hAdaptGrid : ∀ n, Adapted (H n)
      (fun k ω => X.X (clock n k) ω) := by
    intro n k
    exact hAdapt (clock n k)
  have hMartGrid : ∀ n, Martingale
      (fun k ω => Real.exp (-(q * (clock n k : ℝ))) *
        W (x + X.X (clock n k) ω)) (H n) P := by
    intro n
    unfold Martingale at hMart ⊢
    rcases hMart with ⟨ha, hm⟩
    constructor
    · intro k
      exact ha (clock n k)
    · intro i j hij
      exact hm (clock n i) (clock n j) (hMon n hij)
  exact chat03_capped_actual_scale_expectation_identity_of_sampled_martingale
    X q hq W hW hzero θ x hθ hψ lower upper T τ hτ
    mesh hmesh hpos K hK clock hclock H hAdaptGrid hMartGrid hInit
