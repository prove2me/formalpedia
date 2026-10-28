-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_esscher_scaled_subunit_kernel_scale_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:24:23.454079+00:00
-- url     : https://prove2.me/submissions/367394b7-85cc-4a3e-83f6-6715535f4b44

import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_scaled_tail_real_kernel_match
import Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_geometric_scale_pointwise
import Theorems.Thm_AvramDividend_Classical_causal_subunit_any_real_recursion_power_bounds
import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_series_summable
import Theorems.Thm_AvramDividend_Classical_causal_subunit_full_convolution_pointwise_integrable
import Theorems.Thm_AvramDividend_Classical_real_convolution_power_recursion_measurable
import Theorems.Thm_AvramDividend_Classical_causal_continuous_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_from_scaled_kernel_real_density
import Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_full_cumulative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- The drift-normalised canonical Esscher renewal measure supplies the exact scale primitive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧ 0 < ρ ∧ ρ < 1 ∧ 0 < b ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ κ x) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ ∧
      (∀ F : ℕ → ℝ → ℝ,
        F 0 = κ →
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) →
        (∀ x : ℝ, 0 < x →
          IntervalIntegrable
            (fun y : ℝ => b * ∑' n : ℕ,
              if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
        (∀ x : ℝ, 0 < x →
          Real.exp (-(φ * x)) * W x =
            c + ∫ y in (0 : ℝ)..x,
              (b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y))) := by
  obtain ⟨φ, hφ, hroot⟩ := bv_positive_esscher_root X hX q hq hbv
  obtain ⟨κ, ρ, hρpos, hρlt, hcont, hanti, hkzero, hkpos, hkL1,
    hmass, hkmeasure⟩ :=
      bv_esscher_canonical_scaled_tail_real_kernel_match
        X hX hbv q hq φ hφ hroot
  have hδ : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  let b : ℝ := (X.drift)⁻¹
  have hbpos : 0 < b := inv_pos.mpr hδ
  have hc : ENNReal.ofReal b = (ENNReal.ofReal X.drift)⁻¹ :=
    ENNReal.ofReal_inv_of_pos hδ
  refine ⟨φ, b, ρ, b, κ, hφ, hroot, hρpos, hρlt, hbpos, hcont,
    hanti, hkzero, (fun x _ => hkpos x), hkL1, hmass, ?_⟩
  intro F hFzero hFsucc
  obtain ⟨_, hi⟩ :=
    causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
      κ ρ b hρpos hρlt hcont hanti hkzero (fun x _ => hkpos x)
      hkL1 hmass F hFzero hFsucc
  refine ⟨hi, ?_⟩
  obtain ⟨K, m, β, hK, hKac, hm0, hmsucc, hmSf, hβ, _, hβfinite,
    hβneg, _, _, hβscale⟩ :=
      bv_esscher_canonical_geometric_scale_pointwise
        X hX q hq W hW hbv φ hφ hroot
  haveI : SFinite K := by
    rw [hK]
    infer_instance
  have hmeas : Measurable κ :=
    causal_continuous_kernel_measurable κ hcont hkzero
  have hFmeas := real_convolution_power_recursion_measurable
    κ F hmeas hFzero hFsucc
  obtain ⟨_, _, hFpos, hFbound⟩ :=
    causal_subunit_any_real_recursion_power_bounds
      κ ρ F hρpos hρlt hcont hanti hkzero (fun x _ => hkpos x)
      hkL1 hmass hFzero hFsucc
  have hFsupport :=
    causal_full_convolution_powers_zero_nonpositive κ F hkzero hFzero hFsucc
  have hFposAll (n : ℕ) (x : ℝ) : 0 ≤ F n x := by
    by_cases hx : 0 ≤ x
    · exact hFpos n x hx
    · rw [hFsupport n x (le_of_lt (lt_of_not_ge hx))]
  have hFsummable :=
    causal_subunit_shifted_renewal_series_summable
      κ F ρ hρpos hρlt hkzero hFzero hFsucc hFpos hFbound
  have hconv :=
    causal_subunit_full_convolution_pointwise_integrable
      κ ρ F hρpos hρlt hcont hanti hkzero
      (fun x _ => hkpos x) hkL1 hmass hFzero hFsucc
  have hKscaled : (ENNReal.ofReal X.drift)⁻¹ • K =
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (κ y)) := by
    rw [hK]
    exact hkmeasure
  have hβdensity :=
    geometric_renewal_from_scaled_kernel_real_density
      ((ENNReal.ofReal X.drift)⁻¹) K κ F m
      hkpos hFposAll hmeas hFmeas hconv hFsummable
      hFzero hFsucc hKscaled hm0 hmsucc hmSf
  let f : ℝ → ℝ := fun y =>
    ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y
  have hfpos (y : ℝ) : 0 ≤ f y := by
    apply tsum_nonneg
    intro n
    cases n with
    | zero => simp
    | succ n => simpa using hFposAll n y
  have hβrepr : β = ENNReal.ofReal b •
      (Measure.dirac (0 : ℝ) + volume.withDensity
        (fun y : ℝ => ENNReal.ofReal (f y))) := by
    rw [hβ, hβdensity, ← hc]
  intro x hx
  have hfi : IntervalIntegrable f volume 0 x := by
    convert (hi x hx).const_mul b⁻¹ using 1
    funext y
    dsimp [f]
    field_simp [ne_of_gt hbpos]
  have hcum :=
    geometric_atom_plus_real_density_full_cumulative
      b (le_of_lt hbpos) f hfpos β hβrepr hβneg hβfinite x hx hfi
  have hscale := (hβscale x hx).trans hcum
  simpa [f, intervalIntegral.integral_const_mul] using hscale
