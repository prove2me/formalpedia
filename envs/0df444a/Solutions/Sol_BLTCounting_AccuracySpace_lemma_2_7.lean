-- Prove2me | solution 1 for BLTCounting.AccuracySpace.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:10:51.317165+00:00
-- url     : https://prove2.me/submissions/e4465f8c-0233-40d0-be8c-0e42e94007a9

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

open Matrix Complex MeasureTheory BLTCounting.AccuracySpace

namespace AuxLemma27

lemma norm_cexp_I_mul_real (r : ℝ) : ‖cexp (I * (r : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I r

lemma integral_cexp_int (k : ℤ) :
    (∫ θ in (-Real.pi)..Real.pi, cexp (I * (k : ℂ) * (θ : ℂ))) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp [intervalIntegral.integral_const, sub_neg_eq_add]
    ring
  · have hc_ne : I * (k : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hk)
    have hderiv : ∀ θ ∈ Set.uIcc (-Real.pi) Real.pi,
        HasDerivAt (fun x : ℝ => cexp (I * (k : ℂ) * (x : ℂ)) / (I * (k : ℂ)))
          (cexp (I * (k : ℂ) * (θ : ℂ))) θ := by
      intro θ _
      have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 θ := Complex.ofRealCLM.hasDerivAt
      have h2 : HasDerivAt (fun x : ℝ => I * (k : ℂ) * (x : ℂ)) (I * (k : ℂ)) θ := by
        simpa using h1.const_mul (I * (k : ℂ))
      have h3 : HasDerivAt (fun x : ℝ => cexp (I * (k : ℂ) * (x : ℂ)))
          (cexp (I * (k : ℂ) * (θ : ℂ)) * (I * (k : ℂ))) θ := h2.cexp
      have h4 := h3.div_const (I * (k : ℂ))
      rwa [mul_div_cancel_right₀ _ hc_ne] at h4
    have hint : IntervalIntegrable (fun θ : ℝ => cexp (I * (k : ℂ) * (θ : ℂ)))
        volume (-Real.pi) Real.pi :=
      (Continuous.cexp (by continuity)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hper : cexp (I * (k : ℂ) * (Real.pi : ℂ)) =
        cexp (I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
      have hdiff : I * (k : ℂ) * (Real.pi : ℂ) =
          I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
        push_cast
        ring
      rw [hdiff, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I k, mul_one]
    rw [hper, sub_self]

lemma integral_bilateralSymbol_mul (a : ℤ → ℂ) (ha : Summable (fun t => ‖a t‖)) (m : ℤ) :
    (∫ θ in (-Real.pi)..Real.pi, bilateralSymbol a θ * cexp (I * (m : ℂ) * (θ : ℂ))) =
      ((2 * Real.pi : ℝ) : ℂ) * a (-m) := by
  let s : Set ℝ := Set.Ioc (-Real.pi) Real.pi
  let μ : Measure ℝ := volume.restrict s
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [intervalIntegral.integral_of_le hle]
  let f : ℤ → ℝ → ℂ := fun t θ => a t * cexp (I * (((t + m : ℤ) : ℂ)) * (θ : ℂ))
  have hfun : ∀ θ : ℝ, bilateralSymbol a θ * cexp (I * (m : ℂ) * (θ : ℂ)) = ∑' t : ℤ, f t θ := by
    intro θ
    unfold bilateralSymbol
    rw [← tsum_mul_right]
    congr 1
    ext t
    dsimp [f]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hfun]
  have hmeas : ∀ t : ℤ, AEStronglyMeasurable (f t) μ := fun t =>
    (Continuous.mul continuous_const (Continuous.cexp (by continuity))).aestronglyMeasurable
  have hbound : ∑' t : ℤ, ∫⁻ θ, ‖f t θ‖ₑ ∂μ ≠ ⊤ := by
    have hterm : ∀ t : ℤ, (∫⁻ θ, ‖f t θ‖ₑ ∂μ) = ENNReal.ofReal ‖a t‖ * μ Set.univ := by
      intro t
      have hnorm : ∀ θ : ℝ, ‖f t θ‖ₑ = ENNReal.ofReal ‖a t‖ := by
        intro θ
        rw [← ofReal_norm]
        dsimp [f]
        have hr : I * (((t + m : ℤ) : ℂ)) * (θ : ℂ) =
            I * (((((t + m : ℤ) : ℝ) * θ) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [norm_mul, hr, norm_cexp_I_mul_real, mul_one]
      simp_rw [hnorm]
      rw [lintegral_const]
    simp_rw [hterm, ENNReal.tsum_mul_right]
    refine ENNReal.mul_ne_top ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => norm_nonneg _) ha]
      exact ENNReal.ofReal_ne_top
    · rw [Measure.restrict_apply_univ]
      simp [s]
  rw [MeasureTheory.integral_tsum hmeas hbound]
  have heval : ∀ t : ℤ, (∫ θ, f t θ ∂μ) =
      if t = -m then a t * ((2 * Real.pi : ℝ) : ℂ) else 0 := by
    intro t
    change (∫ θ in s, f t θ) = _
    rw [← intervalIntegral.integral_of_le hle]
    dsimp [f]
    rw [intervalIntegral.integral_const_mul, integral_cexp_int (t + m)]
    by_cases htm : t + m = 0
    · have ht : t = -m := by omega
      simp [ht]
    · have ht : t ≠ -m := by omega
      simp [htm, ht]
  simp_rw [heval]
  rw [tsum_ite_eq, mul_comm]

lemma trigPoly_norm_sq {K : ℕ} (u : Fin K → ℂ) (θ : ℝ) :
    ((‖trigPoly u θ‖ ^ 2 : ℝ) : ℂ) =
      ∑ i : Fin K, ∑ j : Fin K,
        star (u i) * u j * cexp (I * ((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℂ) * (θ : ℂ)) := by
  have hconj_mul : ((‖trigPoly u θ‖ ^ 2 : ℝ) : ℂ) = star (trigPoly u θ) * trigPoly u θ := by
    simpa using (Complex.conj_mul' (trigPoly u θ)).symm
  rw [hconj_mul]
  unfold trigPoly
  rw [star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hstar_exp : star (cexp (I * ((i : ℕ) : ℂ) * (θ : ℂ))) =
      cexp (-(I * ((i : ℕ) : ℂ) * (θ : ℂ))) := by
    change (starRingEnd ℂ) (cexp (I * ((i : ℕ) : ℂ) * (θ : ℂ))) = _
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [star_mul', hstar_exp]
  calc
    star (u i) * cexp (-(I * ((i : ℕ) : ℂ) * (θ : ℂ))) * (u j * cexp (I * ((j : ℕ) : ℂ) * (θ : ℂ)))
        = star (u i) * u j *
          (cexp (-(I * ((i : ℕ) : ℂ) * (θ : ℂ))) * cexp (I * ((j : ℕ) : ℂ) * (θ : ℂ))) := by ring
    _ = star (u i) * u j *
        cexp (I * ((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℂ) * (θ : ℂ)) := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

end AuxLemma27

theorem solution (a : ℤ → ℂ) (ha : Summable (fun t => ‖a t‖))
    (hconj : ∀ t, a (-t) = star (a t)) (K : ℕ) (u : Fin K → ℂ) :
    star u ⬝ᵥ (toeplitz K a *ᵥ u) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ θ in (-Real.pi)..Real.pi,
          bilateralSymbol a θ * ((‖trigPoly u θ‖ ^ 2 : ℝ) : ℂ) := by
  have _ := hconj
  have hcont_sym : Continuous (bilateralSymbol a) := by
    unfold bilateralSymbol
    refine continuous_tsum (fun t => Continuous.mul continuous_const (Continuous.cexp (by continuity)))
      ha (fun t θ => ?_)
    have hr : I * (t : ℂ) * (θ : ℂ) = I * ((((t : ℝ) * θ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [norm_mul, hr, AuxLemma27.norm_cexp_I_mul_real, mul_one]
  have hint_ij : ∀ i j : Fin K, IntervalIntegrable
      (fun θ : ℝ => star (u i) * u j *
        (bilateralSymbol a θ * cexp (I * ((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℂ) * (θ : ℂ))))
      volume (-Real.pi) Real.pi := fun i j =>
    (continuous_const.mul (hcont_sym.mul (Continuous.cexp (by continuity)))).intervalIntegrable _ _
  have hrew : (fun θ : ℝ => bilateralSymbol a θ * ((‖trigPoly u θ‖ ^ 2 : ℝ) : ℂ)) =
      fun θ : ℝ => ∑ i : Fin K, ∑ j : Fin K, star (u i) * u j *
        (bilateralSymbol a θ * cexp (I * ((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℂ) * (θ : ℂ))) := by
    ext θ
    rw [AuxLemma27.trigPoly_norm_sq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hrew, intervalIntegral.integral_finsetSum]
  · have hinner : ∀ i : Fin K,
        (∫ θ in (-Real.pi)..Real.pi, ∑ j : Fin K, star (u i) * u j *
          (bilateralSymbol a θ * cexp (I * ((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : ℂ) * (θ : ℂ)))) =
        ∑ j : Fin K, star (u i) * u j *
          (((2 * Real.pi : ℝ) : ℂ) * a (-((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))))) := by
      intro i
      rw [intervalIntegral.integral_finsetSum (fun j _ => hint_ij i j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_const_mul, AuxLemma27.integral_bilateralSymbol_mul a ha]
    simp_rw [hinner]
    rw [Finset.mul_sum]
    simp only [dotProduct, Matrix.mulVec, toeplitz, Matrix.of_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hneg : -((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) = ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) := by ring
    rw [hneg]
    push_cast
    field_simp [ne_of_gt Real.pi_pos]
  · intro i _
    exact (continuous_finsetSum Finset.univ fun j _ =>
      continuous_const.mul (hcont_sym.mul (Continuous.cexp (by continuity)))).intervalIntegrable _ _
