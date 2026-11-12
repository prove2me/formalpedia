-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger161_original_clipped_discount_euler_pathwise_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:29:38.734691+00:00
-- url     : https://prove2.me/submissions/16c7a93e-7eb7-4f55-9269-26b6b9103374

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger111_subclock_le_ruin_and_horizon
import Theorems.Thm_AvramDividend_Classical_avram_gledger162_original_topcap_compact_postpayment_weight_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger164_finite_clipped_discount_weighted_euler_rate
import Theorems.Thm_AvramDividend_Classical_avram_gledger165_uniform_mesh_discount_rate_scaling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let A : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      (∑ i ∈ Finset.range (m + 1),
        (E (v (i + 1)) - E (v i)) * w (Y (v i))) +
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then q * (Δ : ℝ) * E s * w (Y s) else 0
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ᵐ ω ∂P, |A m ω| ≤ K / ((m : ℝ) + 1) := by
  intro A
  obtain ⟨B, hB, hWB⟩ :=
    avram_gledger162_original_topcap_compact_postpayment_weight_uniform_bound
      X w C hTopCap hw_smooth x hx D hD.1.1 ρ j hprefix
  let K : ℝ := (q * (n : ℝ)) ^ 2 * B + 2 * q * (n : ℝ) * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro m
  filter_upwards [hWB] with ω hω
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let W : ℕ → ℝ := fun i =>
    w (x + X.X (min ((i : ℝ≥0) * Δ) (ρ ω)) ω -
      rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω)
  have hρn : ρ ω ≤ (n : ℝ≥0) :=
    (avram_gledger111_subclock_le_ruin_and_horizon
      (ruinTime X x D ω) n (ρ ω) (by simpa [hτeq ω] using hρle ω)).1
  have hW : ∀ i : ℕ, i ≤ m → (i : ℝ≥0) * Δ < ρ ω → |W i| ≤ B := by
    intro i him hi
    have hvi : min ((i : ℝ≥0) * Δ) (ρ ω) = (i : ℝ≥0) * Δ :=
      min_eq_left hi.le
    simpa only [W, hvi] using hω ((i : ℝ≥0) * Δ) hi
  have hfinite :=
    avram_gledger164_finite_clipped_discount_weighted_euler_rate
      n m hn (ρ ω) hρn q B hq.le hB W (by simpa only [Δ] using hW)
  have hnum := avram_gledger165_uniform_mesh_discount_rate_scaling n m q B hB
  have hAeq :
      |A m ω| =
      |(∑ i ∈ Finset.range (m + 1),
          (Real.exp (-(q * ((min (((i+1:ℕ):ℝ≥0)*Δ) (ρ ω) : ℝ≥0) : ℝ))) -
           Real.exp (-(q * ((min ((i:ℝ≥0)*Δ) (ρ ω) : ℝ≥0) : ℝ)))) * W i) +
        ∑ i ∈ Finset.range m,
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          if s < ρ ω then q * (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) * W i else 0| := by
    congr 1
    dsimp [A]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    change ite ((i : ℝ≥0) * Δ < ρ ω) _ (0 : ℝ) =
      ite ((i : ℝ≥0) * Δ < ρ ω) _ 0
    by_cases hs : (i : ℝ≥0) * Δ < ρ ω
    · simpa [hs, W, min_eq_left hs.le, Δ, NNReal.coe_div, NNReal.coe_add]
    · simpa only [if_neg hs]
  calc
    |A m ω| ≤ (m : ℝ) * ((q * (Δ : ℝ)) ^ 2 * B) + 2 * q * (Δ : ℝ) * B := by
      rw [hAeq]
      exact hfinite
    _ ≤ K / ((m : ℝ) + 1) := by
      simpa [K, Δ, NNReal.coe_div, NNReal.coe_add] using hnum
