-- Prove2me | solution 1 for AvramDividend.Classical.bv_root_discounted_tail_kernel_causal_real_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:08:43.023678+00:00
-- url     : https://prove2.me/submissions/caab9bc1-c79e-48da-a111-62b1c5c5a6a2

import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_integrable_real_density
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Modify the finite root-shifted BV Esscher kernel on a null half-line to make it causal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hδ : 0 < X.drift) :
    ∃ (κ : Measure ℝ) (K : ℝ → ℝ),
      SFinite κ ∧ κ ≪ volume ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      Measurable K ∧ (∀ x : ℝ, 0 ≤ K x) ∧
      Integrable K volume ∧ (∀ x : ℝ, x ≤ 0 → K x = 0) ∧
      κ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (K x)) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
              ENNReal.ofReal
                ((1 - Real.exp (-(s * (z : ℝ)))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) := by
  obtain ⟨κ, K, hsf, hac, hsupp, hgap, hMeas, hPos, hInt, hDens, hLap⟩ :=
    bv_root_discounted_tail_kernel_integrable_real_density X hbv q hq φ hφ hroot hδ
  let K' : ℝ → ℝ := fun x => if 0 < x then K x else 0
  have hrepr : K' = (Ioi (0 : ℝ)).indicator K := by
    funext x
    by_cases hx : 0 < x
    · simp [K', Set.indicator, hx]
    · simp [K', Set.indicator, hx]
  have hMeas' : Measurable K' := by
    rw [hrepr]
    exact hMeas.indicator measurableSet_Ioi
  have hInt' : Integrable K' volume := by
    rw [hrepr]
    exact hInt.indicator measurableSet_Ioi
  have hPos' : ∀ x : ℝ, 0 ≤ K' x := by
    intro x
    by_cases hx : 0 < x
    · simpa [K', hx] using hPos x
    · simp [K', hx]
  have hCausal : ∀ x : ℝ, x ≤ 0 → K' x = 0 := by
    intro x hx
    simp [K', not_lt.mpr hx]
  have hzero : κ ({(0 : ℝ)} : Set ℝ) = 0 := hac (by simp)
  have haeneg : ∀ᵐ x ∂κ, x ∉ Iio (0 : ℝ) :=
    (measure_eq_zero_iff_ae_notMem).mp hsupp
  have hae0 : ∀ᵐ x ∂κ, x ≠ (0 : ℝ) := by
    simpa only [Set.mem_singleton_iff] using
      ((measure_eq_zero_iff_ae_notMem).mp hzero)
  have haepos : ∀ᵐ x ∂κ, x ∈ Ioi (0 : ℝ) := by
    filter_upwards [haeneg, hae0] with x hxneg hxzero
    change 0 < x
    have hx : 0 ≤ x := le_of_not_gt hxneg
    exact lt_of_le_of_ne hx (Ne.symm hxzero)
  have hRestr : κ.restrict (Ioi (0 : ℝ)) = κ :=
    Measure.restrict_eq_self_of_ae_mem haepos
  have hDens' :
      κ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (K' x)) := by
    calc
      κ = κ.restrict (Ioi (0 : ℝ)) := hRestr.symm
      _ = (volume.withDensity (fun x : ℝ => ENNReal.ofReal (K x))).restrict
        (Ioi (0 : ℝ)) := by rw [hDens]
      _ = (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (K x)) :=
          restrict_withDensity measurableSet_Ioi _
      _ = volume.withDensity
        ((Ioi (0 : ℝ)).indicator (fun x : ℝ => ENNReal.ofReal (K x))) :=
          (withDensity_indicator measurableSet_Ioi _).symm
      _ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (K' x)) := by
        congr 1
        funext x
        by_cases hx : 0 < x
        · simp [K', Set.indicator, hx]
        · simp [K', Set.indicator, hx]
  exact ⟨κ, K', hsf, hac, hgap, hMeas', hPos', hInt', hCausal, hDens', hLap⟩
