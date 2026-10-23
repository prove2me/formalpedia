-- Prove2me | solution 1 for AvramDividend.Classical.chat03_capped_actual_scale_expectation_identity_of_sampled_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:26:49.459355+00:00
-- url     : https://prove2.me/submissions/20ea4545-a10f-473f-90b3-a4c42da9e372

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_expectation_tendsto_full
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_martingale_identity
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

/-!
The correct conditional bridge from sampled q-scale martingales and
their bounded optional stopping identities to a finite-horizon
continuous two-sided exit expectation identity.
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
    (H : ℕ → Filtration ℕ mΩ)
    (hAdapt : ∀ n, Adapted (H n) (fun k ω => X.X (clock n k) ω))
    (hMart : ∀ n, Martingale
      (fun k ω => Real.exp (-(q * (clock n k : ℝ))) *
        W (x + X.X (clock n k) ω)) (H n) P)
    (hInit : ∀ n, (∫ ω,
      Real.exp (-(q * (clock n 0 : ℝ))) *
        W (x + X.X (clock n 0) ω) ∂P) = W x) :
    (∫ ω, Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
      W (x + X.X (min (τ ω) T) ω) ∂P) = W x := by
  have hKc : ∀ n ω, K n ω = hittingBtwn
      (fun k ξ => max (X.X (clock n k) ξ - upper)
        (lower - X.X (clock n k) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) ω := by
    intro n ω
    rw [hK n ω]
    simpa only [hclock] using
      (chat03_actual_ceiling_capped_grid_clipped_hitting_congr
        X lower upper T (mesh n) (hpos n) ω)
  have hGrid : ∀ n, (∫ ω,
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω) ∂P) = W x := by
    intro n
    have hOS :=
      (chat03_two_sided_grid_stopped_martingale_identity
        (fun k ω => X.X (clock n k) ω)
        (fun k ω => Real.exp (-(q * (clock n k : ℝ))) *
          W (x + X.X (clock n k) ω))
        (hAdapt n) (hMart n) lower upper (Nat.ceil (T / mesh n))).trans (hInit n)
    simp_rw [← hKc n] at hOS
    simpa only [hclock, NNReal.coe_min, NNReal.coe_mul] using hOS
  obtain ⟨_, hlim⟩ :=
    chat03_actual_ceiling_capped_grid_expectation_tendsto_full
      X q hq W hW hzero θ x hθ hψ lower upper T τ hτ mesh hmesh hpos K hK
  have heq : (fun n => ∫ ω,
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω) ∂P) =
      (fun _ : ℕ => W x) := funext hGrid
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
