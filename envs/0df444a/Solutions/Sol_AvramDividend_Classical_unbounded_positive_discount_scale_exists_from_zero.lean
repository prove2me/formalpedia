-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_positive_discount_scale_exists_from_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:37:28.484128+00:00
-- url     : https://prove2.me/submissions/90cd4160-d3fc-4097-a9e4-840b9fa0e376

import Theorems.Thm_AvramDividend_Classical_unbounded_zero_scale_bounded_contractive_kernel
import Theorems.Thm_AvramDividend_Classical_causal_bounded_subunit_neumann_continuity_package
import Theorems.Thm_AvramDividend_Classical_causal_untwisted_monotone_series_package
import Theorems.Thm_AvramDividend_Classical_causal_untwisted_renewal_scale_regular
import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_laplace_geometric
import Theorems.Thm_AvramDividend_Classical_causal_geometric_weighted_series_integrable
import Theorems.Thm_AvramDividend_Classical_causal_resolvent_exponential_renormalisation_integrable
import Theorems.Thm_AvramDividend_Classical_causal_renormalised_resolvent_laplace
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_comm_all_real
import Theorems.Thm_AvramDividend_Classical_causal_monotone_global_extension
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_zero_scale_kernel_tilt_all_parameter_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every unbounded-variation zero scale yields its positive-discount scale by renewal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q : ℝ) (hq : 0 < q) :
    ∃ Wq : ℝ → ℝ, IsScaleFunction X q Wq := by
  obtain ⟨θ, ρ, K, hθ, hψq, hρpos, hρlt,
    hKcont, hKbounded, hKi, hKmass, hKzero, hKpos, hKdef⟩ :=
    unbounded_zero_scale_bounded_contractive_kernel X hnbv W₀ hW₀ q hq
  obtain ⟨F, hF0, hFsucc, hFi, hFcont, hFpos,
    hFzero, hFsum, hFseriescont⟩ :=
    causal_bounded_subunit_neumann_continuity_package
      K ρ hKzero hKcont hKbounded hKi hKpos
      hKmass hρpos hρlt
  have hFrev (n : ℕ) (x : ℝ) : F (n + 1) x =
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * F n s ∂volume := by
    calc
      F (n + 1) x =
          ∫ s in Ioc (0 : ℝ) x, K s * F n (x - s) ∂volume :=
        congrFun (hFsucc n) x
      _ = ∫ s in Ioc (0 : ℝ) x, F n s * K (x - s) ∂volume :=
        causal_Ioc_convolution_comm_all_real K (F n) x
      _ = ∫ s in Ioc (0 : ℝ) x, K (x - s) * F n s ∂volume := by
        congr 1
        funext s
        ring
  let f : ℝ → ℝ := fun x => q * W₀ x
  have hWorigin : W₀ 0 = 0 :=
    unbounded_scale_zero_origin_nonnegative_discount
      X hnbv 0 (le_refl 0) W₀ hW₀
  have hfzero (x : ℝ) (hx : x ≤ 0) : f x = 0 := by
    rcases lt_or_eq_of_le hx with hlt | heq
    · simp [f, hW₀.1 x hlt]
    · subst x
      simp [f, hWorigin]
  have hfpos (x : ℝ) : 0 ≤ f x := by
    by_cases hx : 0 ≤ x
    · exact mul_nonneg (le_of_lt hq) (hW₀.2.1 x hx)
    · simp [f, hW₀.1 x (lt_of_not_ge hx)]
  have hfcont : Continuous f := by
    exact continuous_const.mul
      (scaleFunction_continuous_of_zero_origin X 0 W₀ hW₀ hWorigin)
  have hfmono : Monotone f :=
    causal_monotone_global_extension f
      (fun x hx => hfzero x (le_of_lt hx))
      (fun x _ => hfpos x)
      (by
        intro x hx y hy hxy
        exact mul_le_mul_of_nonneg_left
          (hW₀.2.2.2.1 hx hy hxy) (le_of_lt hq))
  have hKrel (x : ℝ) : K x = Real.exp (-(θ * x)) * f x := by
    rw [hKdef x]
    dsimp [f]
    ring
  obtain ⟨U, hU0, hUrec, hrel, hUcont, hUmono,
    hUsum, hUseriescont, hUseriesmono⟩ :=
    causal_untwisted_monotone_series_package
      f K F θ hfzero hfcont hfpos hfmono
      hKrel hF0 hFrev hFcont hFsum hFseriescont
  obtain ⟨Wq, hWqform, hWqneg, hWqpos, hWqcont, hWqmono⟩ :=
    causal_untwisted_renewal_scale_regular
      F U θ q hq hFzero hrel hUmono hUseriescont hUseriesmono
  refine ⟨Wq, hWqneg, hWqpos, hWqcont, hWqmono, ?_⟩
  intro η hη0 hηψ
  have hψη0 : 0 < X.ψ η := lt_trans hq hηψ
  have hKl :=
    zero_scale_kernel_tilt_all_parameter_laplace
      X W₀ hW₀ q θ η hη0 hψη0
  have hKiη : IntegrableOn
      (fun x : ℝ => Real.exp (-((η - θ) * x)) * K x)
      (Ioi (0 : ℝ)) volume := by
    simpa only [hKdef] using hKl.1
  have hKmassη :
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-((η - θ) * x)) * K x ∂volume) =
        q / X.ψ η := by
    simpa only [hKdef] using hKl.2
  have hFiη :=
    causal_convolution_powers_weighted_integrable
      K F (η - θ) hKiη hF0 hFsucc
  have hFmasses :=
    causal_convolution_powers_laplace_geometric
      K F (η - θ) (q / X.ψ η)
      hKiη hFiη hF0 hFsucc hKmassη
  have hρ0η : 0 ≤ q / X.ψ η :=
    div_nonneg (le_of_lt hq) (le_of_lt hψη0)
  have hρltη : q / X.ψ η < 1 :=
    (div_lt_one hψη0).2 hηψ
  have hweighted :=
    causal_geometric_weighted_series_integrable
      F (η - θ) (q / X.ψ η)
      hρ0η hρltη hFiη hFpos hFsum hFmasses
  have hWqi : IntegrableOn
      (fun x : ℝ => Real.exp (-(η * x)) * Wq x)
      (Ioi (0 : ℝ)) volume := by
    have hi :=
      causal_resolvent_exponential_renormalisation_integrable
        F θ η q hweighted
    simpa only [hWqform] using hi
  have hWqmass :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(η * x)) * Wq x ∂volume) =
        (X.ψ η - q)⁻¹ := by
    have hm :=
      causal_renormalised_resolvent_laplace
        K F θ η q (X.ψ η) hq hηψ
        hKiη hF0 hFsucc hFpos hKmassη
    simpa only [hWqform, one_div] using hm
  exact ⟨hWqi, hWqmass⟩