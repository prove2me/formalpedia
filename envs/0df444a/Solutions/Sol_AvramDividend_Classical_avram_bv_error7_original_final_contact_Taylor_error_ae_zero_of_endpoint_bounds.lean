-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_final_contact_Taylor_error_ae_zero_of_endpoint_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:46:45.497709+00:00
-- url     : https://prove2.me/submissions/64e522eb-8221-4c2a-8a91-77fe5cb0ac34

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_discounted_single_contact_Taylor_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The genuine original final-contact Taylor error is a.e. negligible if
the value function has a uniform one-cell Lipschitz/derivative envelope.
The unique last cell is allowed to touch ruin or the cap boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q L : ℝ) (hq : 0 ≤ q) (hL : 0 ≤ L)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hMesh : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       ∀ δ : ℝ, 0 < δ → ∀ᶠ m in Filter.atTop,
         ∀ i, i < k m ω →
           |Y (u m (i + 1)) - Y (u m i)| < δ))
    (hContact : ∀ m ω, k m ω ≠ 0 →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℝ := x + X.X (u m (k m ω - 1)) ω -
         rightLimit D (u m (k m ω - 1)) ω
       let c : ℝ := Y (u m (k m ω)) - Y (u m (k m ω - 1))
       |w (z + c) - w z| ≤ L * |c| ∧ |deriv w z| ≤ L))
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℝ := x + X.X (u m (k m ω - 1)) ω -
         rightLimit D (u m (k m ω - 1)) ω
       let c : ℝ := Y (u m (k m ω)) - Y (u m (k m ω - 1))
       if k m ω = 0 then 0
       else Real.exp (-(q * (u m (k m ω - 1) : ℝ))) *
         (w (z + c) - w z - deriv w z * c))) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)) := by
  have hInc :=
    avram_bv_error7_original_final_contact_compensated_increment_ae_zero
      X u k hMesh
  filter_upwards [hInc] with ω hω
  let inc : ℕ → ℝ := fun m =>
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
      else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    if k m ω = 0 then 0
    else Y (u m (k m ω)) - Y (u m (k m ω - 1))
  have hTo : Tendsto inc atTop (nhds (0 : ℝ)) := hω
  have hBound (m : ℕ) : |Err m ω| ≤ (2 * L) * |inc m| := by
    by_cases hk : k m ω = 0
    · rw [hSource m ω]
      simp [inc, hk]
    · obtain ⟨hLip, hDeriv⟩ := hContact m ω hk
      dsimp at hLip hDeriv
      have hCell := avram_bv_error7_discounted_single_contact_Taylor_bound
        w q (u m (k m ω - 1) : ℝ)
        (x + X.X (u m (k m ω - 1)) ω -
          rightLimit D (u m (k m ω - 1)) ω)
        ((X.X (u m (k m ω)) ω +
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ u m (k m ω) then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0)) -
          (X.X (u m (k m ω - 1)) ω +
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ u m (k m ω - 1) then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0))) L
        hq (u m (k m ω - 1)).property hL hLip hDeriv
      rw [hSource m ω]
      simpa only [inc, if_neg hk] using hCell
  apply (Metric.tendsto_atTop).2
  intro ε hε
  have hden : 0 < 2 * L + 1 := by positivity
  have hsm : 0 < ε / (2 * L + 1) := div_pos hε hden
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop).1 hTo (ε / (2 * L + 1)) hsm
  refine ⟨N, ?_⟩
  intro m hm
  have hsmall : |inc m| < ε / (2 * L + 1) := by
    simpa only [Real.dist_eq, sub_zero] using hN m hm
  have hb := hBound m
  have hL0 : 0 ≤ 2 * L := by positivity
  have hsmallMul : (2 * L) * |inc m| < ε := by
    have hScaled : (2 * L) * |inc m| ≤
        (2 * L) * (ε / (2 * L + 1)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hsmall) hL0
    calc
      (2 * L) * |inc m| ≤ (2 * L) * (ε / (2 * L + 1)) := hScaled
      _ = (2 * L * ε) / (2 * L + 1) := by ring
      _ < ε := by
        apply (div_lt_iff₀ hden).2
        nlinarith
  have : |Err m ω| < ε := lt_of_le_of_lt hb hsmallMul
  simpa only [Real.dist_eq, sub_zero] using this
