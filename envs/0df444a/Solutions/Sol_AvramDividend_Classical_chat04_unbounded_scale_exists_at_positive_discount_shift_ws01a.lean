-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_scale_exists_at_positive_discount_shift_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:43:15.412599+00:00
-- url     : https://prove2.me/submissions/551f4b0d-1422-46e2-8ed0-53aa3917658b

import Theorems.Thm_AvramDividend_Classical_chat04_positive_discount_shift_bounded_kernel_ws01a
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
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A supplied positive q-scale independently constructs the scale at q+p. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (Wq : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq) (p : ℝ) (hp : 0 < p) :
    ∃ Wqp : ℝ → ℝ, IsScaleFunction X (q + p) Wqp := by
  obtain ⟨θ, ρ, K, hθ, hψ, hρpos, hρlt,
    hKcont, hKbounded, hKi, hKmass, hKzero, hKpos, hKdef⟩ :=
    chat04_positive_discount_shift_bounded_kernel_ws01a
      X hnbv q hq Wq hWq p hp
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
  let f : ℝ → ℝ := fun x => p * Wq x
  have hWorigin : Wq 0 = 0 :=
    unbounded_scale_zero_origin_nonnegative_discount X hnbv q (le_of_lt hq) Wq hWq
  have hfzero (x : ℝ) (hx : x ≤ 0) : f x = 0 := by
    rcases lt_or_eq_of_le hx with hlt | heq
    · simp [f, hWq.1 x hlt]
    · subst x
      simp [f, hWorigin]
  have hfpos (x : ℝ) : 0 ≤ f x := by
    by_cases hx : 0 ≤ x
    · exact mul_nonneg (le_of_lt hp) (hWq.2.1 x hx)
    · simp [f, hWq.1 x (lt_of_not_ge hx)]
  have hfcont : Continuous f :=
    continuous_const.mul (scaleFunction_continuous_of_zero_origin X q Wq hWq hWorigin)
  have hfmono : Monotone f :=
    causal_monotone_global_extension f
      (fun x hx => hfzero x (le_of_lt hx))
      (fun x _ => hfpos x)
      (by
        intro x hx y hy hxy
        exact mul_le_mul_of_nonneg_left
          (hWq.2.2.2.1 hx hy hxy) (le_of_lt hp))
  have hKrel (x : ℝ) : K x = Real.exp (-(θ * x)) * f x := by
    rw [hKdef x]
    dsimp [f]
    ring
  obtain ⟨U, hU0, hUrec, hrel, hUcont, hUmono,
    hUsum, hUseriescont, hUseriesmono⟩ :=
    causal_untwisted_monotone_series_package
      f K F θ hfzero hfcont hfpos hfmono
      hKrel hF0 hFrev hFcont hFsum hFseriescont
  obtain ⟨Wqp, hWqpform, hWqpneg, hWqppos, hWqpcont, hWqpmono⟩ :=
    causal_untwisted_renewal_scale_regular
      F U θ p hp hFzero hrel hUmono hUseriescont hUseriesmono
  refine ⟨Wqp, hWqpneg, hWqppos, hWqpcont, hWqpmono, ?_⟩
  intro η hη0 hηψ
  have hηψq : q < X.ψ η := by linarith
  have hηψdiff : 0 < X.ψ η - q := sub_pos.mpr hηψq
  obtain ⟨hWqiη, hWqmassη⟩ := hWq.2.2.2.2 η hη0 hηψq
  have hKernelAt (x : ℝ) :
      Real.exp (-((η - θ) * x)) * K x =
        p * (Real.exp (-(η * x)) * Wq x) := by
    rw [hKdef x]
    calc
      Real.exp (-((η - θ) * x)) *
          (p * (Real.exp (-(θ * x)) * Wq x)) =
        p * ((Real.exp (-((η - θ) * x)) * Real.exp (-(θ * x))) * Wq x) := by ring
      _ = p * (Real.exp (-(η * x)) * Wq x) := by
        have ha : -((η - θ) * x) + -(θ * x) = -(η * x) := by ring
        rw [← Real.exp_add, ha]
  have hKernelFn :
      (fun x : ℝ => Real.exp (-((η - θ) * x)) * K x) =
        (fun x : ℝ => p * (Real.exp (-(η * x)) * Wq x)) :=
    funext hKernelAt
  have hKiη : IntegrableOn
      (fun x : ℝ => Real.exp (-((η - θ) * x)) * K x)
      (Ioi (0 : ℝ)) volume := by
    rw [hKernelFn]
    change Integrable
      (fun x : ℝ => p * (Real.exp (-(η * x)) * Wq x))
      (volume.restrict (Ioi (0 : ℝ)))
    exact hWqiη.const_mul p
  have hKmassη : (∫ x in Ioi (0 : ℝ),
      Real.exp (-((η - θ) * x)) * K x ∂volume) = p / (X.ψ η - q) := by
    rw [hKernelFn, integral_const_mul, hWqmassη]
    simp only [div_eq_mul_inv]
  have hFiη := causal_convolution_powers_weighted_integrable
    K F (η - θ) hKiη hF0 hFsucc
  have hFmasses :=
    causal_convolution_powers_laplace_geometric
      K F (η - θ) (p / (X.ψ η - q))
      hKiη hFiη hF0 hFsucc hKmassη
  have hρ0η : 0 ≤ p / (X.ψ η - q) :=
    div_nonneg (le_of_lt hp) (le_of_lt hηψdiff)
  have hρltη : p / (X.ψ η - q) < 1 :=
    (div_lt_one hηψdiff).2 (by linarith)
  have hweighted :=
    causal_geometric_weighted_series_integrable
      F (η - θ) (p / (X.ψ η - q))
      hρ0η hρltη hFiη hFpos hFsum hFmasses
  have hWqpi : IntegrableOn
      (fun x : ℝ => Real.exp (-(η * x)) * Wqp x)
      (Ioi (0 : ℝ)) volume := by
    have hi :=
      causal_resolvent_exponential_renormalisation_integrable
        F θ η p hweighted
    simpa only [hWqpform] using hi
  have hWqpmass :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(η * x)) * Wqp x ∂volume) =
        (X.ψ η - (q + p))⁻¹ := by
    have hm :=
      causal_renormalised_resolvent_laplace
        K F θ η p (X.ψ η - q) hp (by linarith)
        hKiη hF0 hFsucc hFpos hKmassη
    simpa only [hWqpform, one_div, sub_sub, add_assoc, add_comm, add_left_comm]
      using hm
  exact ⟨hWqpi, hWqpmass⟩
