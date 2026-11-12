-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger77_original_topcap_stopped_cash_source_pointwise_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:18:41.796942+00:00
-- url     : https://prove2.me/submissions/97e1dc0c-0428-46e7-9b5d-bc1ced60b008

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger35_original_clipped_uniform_four_event_telescope
import Theorems.Thm_AvramDividend_Classical_avram_gledger81_original_stopped_dividend_contact_mesh_correction
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit false in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let H : Ω → ℝ := fun ω =>
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    ∀ m : ℕ, ∀ᵐ ω ∂P,
      max (H ω - w x - S (m + 1) ω) (0 : ℝ) ≤ B m ω := by
  intro H S B m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
  let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (v i ω) ω - rightLimit D (v i ω) ω
  let Z : ℕ → Ω → ℝ := fun i ω => x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
  let F : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  let Contact : Ω → ℝ := fun ω =>
    (w (x - rightLimit D 0 ω) - w x) +
    Finset.sum (Finset.range (m + 2)) (fun i =>
      E (v (i + 1) ω) *
        ((w (riskProcess X x D (v (i + 1) ω) ω) - w (Z i ω)) +
          (w (Y (i + 1) ω) -
            w (riskProcess X x D (v (i + 1) ω) ω)))) +
    E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) -
      w (x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω)) + F ω
  have hContact : ∀ᵐ ω ∂P, max (Contact ω) 0 ≤ B m ω := by
    simpa only [Contact, B, Δ, v, E, Y, Z, F] using
      (avram_gledger81_original_stopped_dividend_contact_mesh_correction
        X hX q hq w C hC hTopCap hw0 hw_cont hw_neg hw_grad
        x hx hxc D hD hjump n hn τ hτeq ρ hρstop hρle j hprefix m)
  have hρbound (ω : Ω) : ρ ω ≤ (n : ℝ≥0) :=
    (hρle ω).trans (by
      rw [hτeq ω]
      exact ENNReal.toNNReal_mono (by simp) (min_le_right _ _))
  have hρruin (ω : Ω) : (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    calc
      (ρ ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by exact_mod_cast hρle ω
      _ = min (ruinTime X x D ω) (n : ℝ≥0∞) := by rw [hτeq ω]; simp [ENNReal.coe_toNNReal]
      _ ≤ ruinTime X x D ω := min_le_left _ _
  filter_upwards [hContact] with ω hc
  have hTel :=
    avram_gledger35_original_clipped_uniform_four_event_telescope
      X x q D hD.1.1 w n (m + 1) ρ hρruin hρbound ω
  have hm : (m + 1) + 1 = m + 2 := by omega
  have hSum :
      (Finset.sum (Finset.range (m + 2)) (fun i =>
        (E (v (i + 1) ω) - E (v i ω)) * w (Y i ω) +
          E (v (i + 1) ω) * (w (Z i ω) - w (Y i ω)) +
          E (v (i + 1) ω) *
            (w (riskProcess X x D (v (i + 1) ω) ω) - w (Z i ω)) +
          E (v (i + 1) ω) *
            (w (Y (i + 1) ω) -
              w (riskProcess X x D (v (i + 1) ω) ω)))) =
        S (m + 1) ω +
          Finset.sum (Finset.range (m + 2)) (fun i =>
            E (v (i + 1) ω) *
              ((w (riskProcess X x D (v (i + 1) ω) ω) - w (Z i ω)) +
                (w (Y (i + 1) ω) -
                  w (riskProcess X x D (v (i + 1) ω) ω)))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [S, Δ, v, E, Y, Z]
    simp only [hm, Nat.cast_add, Nat.cast_one]
    ring
  have hTel' : E (ρ ω) * w (riskProcess X x D (ρ ω) ω) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
        S (m + 1) ω +
        Finset.sum (Finset.range (m + 2)) (fun i =>
          E (v (i + 1) ω) *
            ((w (riskProcess X x D (v (i + 1) ω) ω) - w (Z i ω)) +
              (w (Y (i + 1) ω) -
                w (riskProcess X x D (v (i + 1) ω) ω)))) +
        E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) -
          w (x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω)) := by
    have hNN : ((m + 1 : ℕ) : ℝ≥0) + 1 = (m : ℝ≥0) + 2 := by push_cast; ring
    simp only [hm, hNN] at hTel
    dsimp [Δ, v, E, Y, Z] at hTel hSum ⊢
    linarith [hTel, hSum]
  by_cases hzero : ρ ω = 0
  · have hs0 : S (m + 1) ω = 0 := by
      dsimp [S]
      apply Finset.sum_eq_zero
      intro i hi; simp [hzero]
    simpa [H, hzero, hs0] using
      (le_max_right (Contact ω) (0 : ℝ)).trans hc
  · have hEq : H ω - w x - S (m + 1) ω = Contact ω := by
      simp only [H, if_neg hzero, Contact]; dsimp [F]; linarith [hTel']
    simpa only [hEq] using hc
