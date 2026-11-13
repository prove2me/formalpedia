-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva62_original_BV_canonical_compensated_uniform_grid_exact_positive_cash_excess_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:25:40.641203+00:00
-- url     : https://prove2.me/submissions/245a63b2-d0f4-4f10-b085-245655161edb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva63_original_BV_spatial_error_explicit_ruin_contact
import Theorems.Thm_AvramDividend_Classical_avram_bva64_original_uniform_ruin_contact_L1_and_mean_vanish
import Theorems.Thm_AvramDividend_Classical_avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bva60_original_BV_any_cofinal_band_uniform_compensated_jump_integrable_centered
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_positive_errors_exact_excess_L1_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 < T) (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) (u : ℕ → ℕ → ℝ≥0) (hu0 : ∀ n, u n 0 = 0) (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2) (hab : ∀ n, a n ≤ b n) (hinside : ∀ n, Icc (a n / 2) (b n) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal + (if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    let N : ℕ → Ω → ℝ := fun n ω =>
      let M : ℝ≥0 → Ω → ℝ := fun S ω =>
        let τ : Ω → ℝ≥0 := fun ω' =>
          (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧ Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
        let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => if p.1 ∈ E ∧ p.2 < 0 then Real.exp (-(q * (p.1.1 : ℝ))) * (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0
        let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' => ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v ≠ 0}).map (fun v : ℝ≥0 => (v, X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v)))
        (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
      (Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω)) + (0 : ℝ)
    Tendsto (fun m =>
      ∫ ω, max (F m ω - (w x + N m ω)) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  intro δ S F N
  let Contact : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal - δ n)
          ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  obtain ⟨ErrSpatial, hErrInt, hBudget, hErrZero⟩ :=
    avram_bva63_original_BV_spatial_error_explicit_ruin_contact
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
      hInfinite u hu0 huniform a b ha ha2 hab hinside hcover
  have hFL1 (m : ℕ) : Integrable (F m) P := by
    simpa only [F, δ, S] using
      (avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite m)
  have hNL1 (m : ℕ) : Integrable (N m) P := by
    exact (avram_bva60_original_BV_any_cofinal_band_uniform_compensated_jump_integrable_centered
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
      hInfinite u hu0 huniform a b ha ha2 hab hinside hcover m).1
  have hContactCore :=
    avram_bva64_original_uniform_ruin_contact_L1_and_mean_vanish
      X x C D hD q (le_of_lt hq) S (by exact_mod_cast hT)
  have hCInt (m : ℕ) : Integrable (Contact m) P := by
    exact hContactCore.1 m
  have hCZero : Tendsto (fun m => ∫ ω, Contact m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
    exact hContactCore.2
  have hCNonneg (m : ℕ) (ω : Ω) : 0 ≤ Contact m ω :=
    ENNReal.toReal_nonneg
  have hCPosInt (m : ℕ) :
      Integrable (fun ω => max (Contact m ω) 0) P := by
    convert hCInt m using 1
    funext ω
    exact max_eq_left (hCNonneg m ω)
  have hCPosZero :
      Tendsto (fun m => ∫ ω, max (Contact m ω) 0 ∂P) atTop (𝓝 (0 : ℝ)) := by
    have heq (m : ℕ) : (∫ ω, max (Contact m ω) 0 ∂P) =
        ∫ ω, Contact m ω ∂P := by
      congr 1
      funext ω
      exact max_eq_left (hCNonneg m ω)
    simpa only [heq] using hCZero
  have hMeas (m : ℕ) :
      AEStronglyMeasurable (fun ω => max (F m ω - (w x + (N m ω + 0))) 0) P := by
    have hBase : AEStronglyMeasurable
        (fun ω : Ω => w x + (N m ω + 0)) P :=
      aestronglyMeasurable_const.add
        ((hNL1 m).aestronglyMeasurable.add aestronglyMeasurable_const)
    exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
      ((hFL1 m).aestronglyMeasurable.sub hBase)
  have hCash (m : ℕ) :
      ∀ᵐ ω ∂P, F m ω ≤ w x + (N m ω + 0) +
        max (ErrSpatial m ω) 0 + max (Contact m ω) 0 := by
    filter_upwards [hBudget m] with ω hh
    have hc : Contact m ω ≤ max (Contact m ω) 0 := le_max_left _ _
    linarith
  simpa only [add_zero] using (avram_bv_strict10_two_positive_errors_exact_excess_L1_tendsto
    P F N (fun _ _ => 0) ErrSpatial Contact (w x)
    hErrInt hCPosInt hMeas hCash hErrZero hCPosZero).2
