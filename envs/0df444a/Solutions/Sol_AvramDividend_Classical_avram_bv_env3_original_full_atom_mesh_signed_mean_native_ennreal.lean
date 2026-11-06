-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_full_atom_mesh_signed_mean_native_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:57:30.515383+00:00
-- url     : https://prove2.me/submissions/fa3e4952-9d2e-454b-b47a-04e8c0e3ea2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_mesh_pathwise_signed_upper_bound_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_deterministic_horizon_real_cash_budget_to_ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (M B : Ω → ℝ) (Mmesh Bmesh : ℕ → Ω → ℝ)
    (hMesh : ∀ᵐ ω ∂P, ∀ n,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T, ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X ⟨T, hT⟩ ω - rightLimit D ⟨T, hT⟩ ω)
      else 0) ≤ w x + Mmesh n ω + Bmesh n ω)
    (hMLim : ∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMint : Integrable M P) (hBint : Integrable B P)
    (hSigned : (∫ ω, M ω + B ω ∂P) ≤ 0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let S : ℝ≥0 := ⟨T, hT⟩
  let Cash : Ω → ℝ := fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T, ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) else 0
  have hCashI : Integrable Cash P := (avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1 X hBV q w hw_cont hw_neg x C D hD T hT).1
  have hTermI : Integrable Term P := (avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad x D hD T hT hTpos).1
  have hJointI : Integrable (fun ω => Cash ω + Term ω) P := hCashI.add hTermI
  have hDomI : Integrable (fun ω => w x + M ω + B ω) P := ((integrable_const (w x)).add hMint).add hBint
  have hMeshTyped : ∀ᵐ ω ∂P, ∀ n,
      Cash ω + Term ω ≤ w x + Mmesh n ω + Bmesh n ω := by
    filter_upwards [hMesh] with ω hω
    intro n
    simpa only [Cash, Term, S] using hω n
  have hMeshLimit : ∀ᵐ ω ∂P, Cash ω + Term ω ≤ w x + M ω + B ω :=
    avram_p3_bv_original_mesh_pathwise_signed_upper_bound_limit
      P (fun ω => Cash ω + Term ω) M B Mmesh Bmesh (w x) hMeshTyped hMLim hBLim
  have hTermNonneg : ∀ ω, 0 ≤ Term ω := by
    intro ω
    have hEq := avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
      X q w C hC hw_cont hw0 hw_smooth hw_grad x hxc D hD (fun _ => S) ω
    change (if (S : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω))
      else 0) = Term ω at hEq
    rw [← hEq]
    split_ifs
    · exact le_max_left _ _
    · exact le_refl _
  have hCashLeJoint : (∫ ω, Cash ω ∂P) ≤ (∫ ω, Cash ω + Term ω ∂P) := by
    apply integral_mono_ae hCashI hJointI
    exact Filter.Eventually.of_forall (fun ω => le_add_of_nonneg_right (hTermNonneg ω))
  have hJointLeDom : (∫ ω, Cash ω + Term ω ∂P) ≤
      (∫ ω, w x + M ω + B ω ∂P) := integral_mono_ae hJointI hDomI hMeshLimit
  have hMeanDom : (∫ ω, w x + M ω + B ω ∂P) =
      w x + (∫ ω, M ω + B ω ∂P) := by
    calc
      _ = (∫ ω, w x + (M ω + B ω) ∂P) := by congr 1; funext ω; ring
      _ = (∫ ω, w x ∂P) + (∫ ω, M ω + B ω ∂P) :=
        integral_add (integrable_const (w x)) (hMint.add hBint)
      _ = _ := by simp
  have hRealCash : (∫ ω, Cash ω ∂P) ≤ w x := by
    calc
      _ ≤ (∫ ω, Cash ω + Term ω ∂P) := hCashLeJoint
      _ ≤ (∫ ω, w x + M ω + B ω ∂P) := hJointLeDom
      _ = w x + (∫ ω, M ω + B ω ∂P) := hMeanDom
      _ ≤ w x := by linarith only [hSigned]
  exact avram_chat07b_original_deterministic_horizon_real_cash_budget_to_ENNReal X x C D hD q T (w x) hT hRealCash
