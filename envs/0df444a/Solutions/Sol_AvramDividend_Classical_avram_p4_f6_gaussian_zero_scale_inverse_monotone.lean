-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_gaussian_zero_scale_inverse_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:40:51.419963+00:00
-- url     : https://prove2.me/submissions/631a9aaf-af48-46b1-9037-09479c32a922
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_ladder_renewal_measure_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_atomless_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_exponential_tonelli
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
import Theorems.Thm_AvramDividend_Classical_psi_eventually_positive_quadratic_of_gaussian

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ)
    (W₀ : ℝ → ℝ)
    (hSupp : ∀ y < 0, W₀ y = 0)
    (hNonneg : ∀ y, 0 ≤ y → 0 ≤ W₀ y)
    (hCont : ContinuousOn W₀ (Ici 0))
    (hLap : ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y => Real.exp (-(θ * y)) * W₀ y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * W₀ y = (X.ψ θ)⁻¹) :
    MonotoneOn W₀ (Ici 0) := by
  obtain ⟨β, C, hβ0, hC0, hψ⟩ :=
    psi_eventually_positive_quadratic_of_gaussian X 0 hσ
  obtain ⟨ν, hνsupp, hνatom, hνfin, hνlap⟩ :=
    avram_p4_f6_gaussian_zero_ladder_renewal_measure_exists X hX hσ
  let F : ℝ → ℝ := fun x =>
    if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0
  have hFcont : ContinuousOn F (Ici (0 : ℝ)) := by
    exact avram_p4_f6_renewal_cdf_atomless_continuous ν hνatom hνfin
  have hFnonneg : ∀ x : ℝ, 0 < x → 0 ≤ F x := by
    intro x hx
    change 0 ≤ if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0
    rw [if_pos (le_of_lt hx)]
    exact ENNReal.toReal_nonneg
  have hFLap :=
    avram_p4_f6_renewal_cdf_exponential_tonelli X hX hσ ν hνsupp hνfin hνlap
  have hEqPos : ∀ x : ℝ, 0 < x → W₀ x = F x := by
    apply continuousOn_Ioi_eq_of_laplace_eq W₀ F β
      (hCont.mono (by intro x hx; change 0 < x at hx; exact le_of_lt hx))
      (hFcont.mono (by intro x hx; change 0 < x at hx; exact le_of_lt hx))
      (by intro x hx; exact hNonneg x (le_of_lt hx))
      hFnonneg
    intro θ hθ
    have hθ0 : 0 ≤ θ := le_trans hβ0 (le_of_lt hθ)
    have hψpos : 0 < X.ψ θ := (hψ θ (le_of_lt hθ)).1
    obtain ⟨hWi, hWeq⟩ := hLap θ hθ0 hψpos
    obtain ⟨hFi, hFeq⟩ := hFLap θ hθ0 hψpos
    refine ⟨?_, ?_, ?_⟩
    · simpa only [neg_mul] using hWi
    · simpa only [F, neg_mul] using hFi
    · calc
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * W₀ x) =
            (X.ψ θ)⁻¹ := by
          simpa only [neg_mul] using hWeq
        _ = (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * F x) := by
          simpa only [F, neg_mul] using hFeq.symm
  have hEqAll : Set.EqOn W₀ F (Ici (0 : ℝ)) := by
    apply Set.EqOn.of_subset_closure
      (fun x hx => by
        change 0 < x at hx
        exact hEqPos x hx) hCont hFcont
    · intro x hx
      change 0 < x at hx
      exact le_of_lt hx
    · change Ici (0 : ℝ) ⊆ closure (Ioi (0 : ℝ))
      simpa only [closure_Ioi] using (subset_rfl : Ici (0 : ℝ) ⊆ Ici (0 : ℝ))
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  rw [hEqAll hx, hEqAll hy]
  change (if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0) ≤
    (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0)
  rw [if_pos hx, if_pos hy]
  apply ENNReal.toReal_mono (ne_of_lt (hνfin y hy))
  exact measure_mono (by
    intro z hz
    exact ⟨hz.1, le_trans hz.2 hxy⟩)
