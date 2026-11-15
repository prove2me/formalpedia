-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a319_original_true_fullcell_rare_positive_two_source_all_mesh_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:23:59.549191+00:00
-- url     : https://prove2.me/submissions/4aa47ee5-7193-4eca-a849-e8dfce009498

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a301_true_fullcell_discounted_positive_scalar_HJB_source_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ga_a306_original_true_fullcell_preincrement_reserve_uniform_upper
import Theorems.Thm_AvramDividend_Classical_avram_ga_a318_compact_HJB_finite_combined_positive_two_stream_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let B : ℝ := x + ((j : ℝ)+1)
    let Large : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0)+1)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0)*Δ
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q*(t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω-rightLimit D t ω
      let R : ℕ → ℝ := fun i => X.X (s i+Δ) ω-X.X (s i) ω
      let Z : ℕ → ℝ := fun i => R i-(Δ : ℝ)*X.c
      ∑ i ∈ Finset.range m,
        if (s i < ρ ω ∧ s i+Δ ≤ ρ ω) ∧ δ ≤ |R i| then
          E (s i+Δ)*(w (Y (s i)+R i)-w (Y (s i))) -
          E (s i)*(deriv w (Y (s i))*R i +
              iteratedDeriv 2 w (Y (s i))/2*(Z i)^2)
        else 0
    let Poly : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0)+1)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0)*Δ
      let R : ℕ → ℝ := fun i => X.X (s i+Δ) ω-X.X (s i) ω
      let Z : ℕ → ℝ := fun i => R i-(Δ : ℝ)*X.c
      ∑ i ∈ Finset.range m,
        if (s i < ρ ω ∧ s i+Δ ≤ ρ ω) ∧ δ ≤ |R i|
        then 1+|R i|+(Z i)^2/2 else 0
    ∃ θ K M : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ δ : ℝ, 0 < δ → ∀ m : ℕ, ∀ᵐ ω ∂P,
        max (Large δ m ω) 0 ≤
          (K*Real.exp (θ*B))*
            (∑ i ∈ Finset.range m,
              let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0)+1)
              let s : ℝ≥0 := (i : ℝ≥0)*Δ
              let R : ℝ := X.X (s+Δ) ω-X.X s ω
              if (s < ρ ω ∧ s+Δ ≤ ρ ω) ∧ δ ≤ |R|
              then Real.exp (θ*R) else 0) +
          M*Poly δ m ω := by
  classical
  intro B Large Poly
  obtain ⟨θ,K,M,hθ,hK,hM,hCell⟩ :=
    avram_ga_a301_true_fullcell_discounted_positive_scalar_HJB_source_envelope
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  have hReserve :=
    (avram_ga_a306_original_true_fullcell_preincrement_reserve_uniform_upper
      X x hx D hD.1.1 n ρ j hprefix).2
  refine ⟨θ,K,M,hθ,hK,hM,?_⟩
  intro δ hδ m
  filter_upwards [hCell m,hReserve m] with ω hc hu
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0)+1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0)*Δ
  let r : ℕ → ℝ := fun i => X.X (s i+Δ) ω-X.X (s i) ω
  let z : ℕ → ℝ := fun i => r i-(Δ : ℝ)*X.c
  let y : ℕ → ℝ := fun i => x+X.X (s i) ω-rightLimit D (s i) ω
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q*(t : ℝ)))
  let A : ℕ → Prop := fun i =>
    (s i < ρ ω ∧ s i+Δ ≤ ρ ω) ∧ δ ≤ |r i|
  let f : ℕ → ℝ := fun i =>
    E (s i+Δ)*(w (y i+r i)-w (y i)) -
    E (s i)*(deriv w (y i)*r i + iteratedDeriv 2 w (y i)/2*(z i)^2)
  have hCell' (i : ℕ) (hi : i ∈ Finset.range m) (ha : A i) :
      max (f i) 0 ≤ K*Real.exp (θ*(y i+r i)) +
        M*(1+|r i|+(z i)^2/2) := (hc i hi) ha.1
  have hReserve' (i : ℕ) (hi : i ∈ Finset.range m) (ha : A i) :
      y i ≤ B := (hu i hi) ha.1.1
  have hSum :=
    avram_ga_a318_compact_HJB_finite_combined_positive_two_stream_upper
      (Finset.range m) A f r z y θ K M B
      hθ hK hM hCell' hReserve'
  exact hSum
