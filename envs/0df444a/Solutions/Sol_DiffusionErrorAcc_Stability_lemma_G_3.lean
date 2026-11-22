-- Prove2me | solution 1 for DiffusionErrorAcc.Stability.lemma_G_3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T01:57:06.749678+00:00
-- url     : https://prove2.me/submissions/c45f66ef-d37b-4086-808b-cd33361103de

import Mathlib
open MeasureTheory InformationTheory
open scoped ENNReal

theorem solution {X : Type*} [MeasurableSpace X] (lam : Measure X)
    (pμ pν : X → ℝ) (hpμm : Measurable pμ) (hpνm : Measurable pν)
    (hpμ : ∀ x, 0 < pμ x) (hpν : ∀ x, 0 < pν x)
    (hpμ1 : ∫ x, pμ x ∂lam = 1) (hpν1 : ∫ x, pν x ∂lam = 1)
    (hpμi : Integrable pμ lam) (hpνi : Integrable pν lam)
    (f : X → ℝ) (hfm : Measurable f) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hKL : klDiv (lam.withDensity fun x => ENNReal.ofReal (pμ x))
      (lam.withDensity fun x => ENNReal.ofReal (pν x)) ≠ ∞) :
    (∫ x, f x ∂(lam.withDensity fun x => ENNReal.ofReal (pν x))) -
        ∫ x, f x ∂(lam.withDensity fun x => ENNReal.ofReal (pμ x)) ≤
      (∫ x, f x * Real.log (pν x / pμ x) ∂(lam.withDensity fun x => ENNReal.ofReal (pμ x))) +
        (klDiv (lam.withDensity fun x => ENNReal.ofReal (pμ x))
          (lam.withDensity fun x => ENNReal.ofReal (pν x))).toReal := by
  set μ : Measure X := lam.withDensity (fun x => ENNReal.ofReal (pμ x)) with hμ
  set ν : Measure X := lam.withDensity (fun x => ENNReal.ofReal (pν x)) with hν
  set L : X → ℝ := fun x => Real.log (pν x / pμ x) with hL
  set L' : X → ℝ := fun x => Real.log (pμ x / pν x) with hL'
  have hofμ_lt : ∀ᵐ x ∂lam, ENNReal.ofReal (pμ x) < ∞ := ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have hofν_lt : ∀ᵐ x ∂lam, ENNReal.ofReal (pν x) < ∞ := ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have hμ_univ : μ Set.univ = 1 := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hpμi (ae_of_all _ fun x => (hpμ x).le)]
    rw [hpμ1]
    simp
  have hν_univ : ν Set.univ = 1 := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hpνi (ae_of_all _ fun x => (hpν x).le)]
    rw [hpν1]
    simp
  have hμ_fin : IsFiniteMeasure μ := ⟨by rw [hμ_univ]; exact ENNReal.one_lt_top⟩
  have hν_fin : IsFiniteMeasure ν := ⟨by rw [hν_univ]; exact ENNReal.one_lt_top⟩
  -- Change of density, integrated against lam
  have hint_ν : ∀ g : X → ℝ, ∫ x, g x ∂ν = ∫ x, pν x * g x ∂lam := by
    intro g
    rw [hν, integral_withDensity_eq_integral_toReal_smul hpνm.ennreal_ofReal hofν_lt]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hpν x).le, smul_eq_mul]
  have hint_μ : ∀ g : X → ℝ, ∫ x, g x ∂μ = ∫ x, pμ x * g x ∂lam := by
    intro g
    rw [hμ, integral_withDensity_eq_integral_toReal_smul hpμm.ennreal_ofReal hofμ_lt]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hpμ x).le, smul_eq_mul]
  -- KL finiteness
  have hKL' : μ ≪ ν ∧ Integrable (llr μ ν) μ := klDiv_ne_top_iff.mp hKL
  -- The density of mu with respect to nu is pμ/pν
  have hdens : ν.withDensity (fun x => ENNReal.ofReal (pμ x / pν x)) = μ := by
    rw [hν, hμ, ← withDensity_mul]
    · congr 1
      funext x
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (hpν x).le]
      congr 1
      have hne : pν x ≠ 0 := (hpν x).ne'
      field_simp
    · exact hpνm.ennreal_ofReal
    · exact (hpμm.div hpνm).ennreal_ofReal
  have hrnd : μ.rnDeriv ν =ᵐ[ν] fun x => ENNReal.ofReal (pμ x / pν x) := by
    have h := Measure.rnDeriv_withDensity ν (f := fun x => ENNReal.ofReal (pμ x / pν x))
      ((hpμm.div hpνm).ennreal_ofReal)
    rwa [hdens] at h
  have hllr_eq : llr μ ν =ᵐ[μ] L' := by
    filter_upwards [hKL'.1.ae_le hrnd] with x hx
    change Real.log ((μ.rnDeriv ν) x).toReal = L' x
    rw [hx, ENNReal.toReal_ofReal (div_pos (hpμ x) (hpν x)).le, hL']
  have hllr_eq_lam : llr μ ν =ᵐ[lam] L' := by
    have h := hllr_eq
    rw [hμ] at h
    rw [Filter.EventuallyEq, ae_withDensity_iff hpμm.ennreal_ofReal] at h
    rw [Filter.EventuallyEq]
    filter_upwards [h] with x hx
    exact hx (by rw [ENNReal.ofReal_ne_zero_iff]; exact hpμ x)
  -- KL term as an integral against lam
  have hkl_int : (klDiv μ ν).toReal = ∫ x, pμ x * L' x ∂lam := by
    rw [toReal_klDiv_of_measure_eq hKL'.1 (by rw [hμ_univ, hν_univ])]
    rw [integral_congr_ae hllr_eq]
    rw [hint_μ]
  -- Integrability
  have hf_bdd : ∀ᵐ x ∂lam, ‖f x‖ ≤ 1 := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf x).1]
    exact (hf x).2
  have hint_pνf : Integrable (fun x => pν x * f x) lam :=
    hpνi.mul_bdd hfm.aestronglyMeasurable hf_bdd
  have hint_pμf : Integrable (fun x => pμ x * f x) lam :=
    hpμi.mul_bdd hfm.aestronglyMeasurable hf_bdd
  have hint_llr_μ : Integrable (fun x => llr μ ν x * pμ x) lam := by
    have h := (integrable_withDensity_iff hpμm.ennreal_ofReal hofμ_lt).mp hKL'.2
    refine h.congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hpμ x).le]
  have hint_pμL' : Integrable (fun x => pμ x * L' x) lam := by
    have h1 : Integrable (fun x => L' x * pμ x) lam := by
      refine hint_llr_μ.congr ?_
      filter_upwards [hllr_eq_lam] with x hx
      rw [hx]
    simpa [mul_comm] using h1
  have hLL' : ∀ x, L' x = -L x := by
    intro x
    change Real.log (pμ x / pν x) = -Real.log (pν x / pμ x)
    rw [Real.log_div (hpμ x).ne' (hpν x).ne',
      Real.log_div (hpν x).ne' (hpμ x).ne']
    ring
  have hint_pμL : Integrable (fun x => pμ x * L x) lam := by
    refine (hint_pμL'.neg).congr ?_
    filter_upwards with x
    rw [Pi.neg_apply, hLL']
    ring
  have hint_pμfL : Integrable (fun x => pμ x * (f x * L x)) lam := by
    have h1 := hint_pμL.mul_bdd hfm.aestronglyMeasurable hf_bdd
    refine h1.congr ?_
    filter_upwards with x
    ring
  -- The pointwise sign
  set K : X → ℝ := fun x => pμ x * ((f x - 1) * ((pν x / pμ x - 1) - L x)) with hK
  have hK_nonpos : K ≤ 0 := by
    intro x
    have h1 : f x - 1 ≤ 0 := by linarith [(hf x).2]
    have h2 : 0 < pν x / pμ x := div_pos (hpν x) (hpμ x)
    have h3 : L x ≤ pν x / pμ x - 1 := by
      rw [hL]
      exact Real.log_le_sub_one_of_pos h2
    have h4 : 0 ≤ (pν x / pμ x - 1) - L x := by linarith
    have h5 : pμ x * ((f x - 1) * ((pν x / pμ x - 1) - L x)) ≤ 0 := by
      have h6 : (f x - 1) * ((pν x / pμ x - 1) - L x) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h1 h4
      exact mul_nonpos_of_nonneg_of_nonpos (hpμ x).le h6
    simpa [hK] using h5
  -- The pointwise identity behind the integral comparison
  have hK_pt : ∀ x,
      ((((pν x * f x - pμ x * f x) - pμ x * (f x * L x)) - pμ x * L' x) - K x) =
        pν x - pμ x := by
    intro x
    have hpm : pμ x ≠ 0 := (hpμ x).ne'
    rw [hLL' x, hK]
    simp only
    field_simp [hpm]
    ring
  -- Integrability of the combinations
  have hFG_int : Integrable (fun x => pν x * f x - pμ x * f x) lam :=
    hint_pνf.sub hint_pμf
  have hFGH_int : Integrable (fun x => (pν x * f x - pμ x * f x) - pμ x * (f x * L x)) lam :=
    hFG_int.sub hint_pμfL
  have hFGHH_int : Integrable (fun x => ((pν x * f x - pμ x * f x) - pμ x * (f x * L x)) - pμ x * L' x) lam :=
    hFGH_int.sub hint_pμL'
  have hK_int : Integrable K lam := by
    have h : Integrable (fun x => ((pν x * f x - pμ x * f x) - pμ x * (f x * L x)) - pμ x * L' x - (pν x - pμ x)) lam :=
      hFGHH_int.sub (hpνi.sub hpμi)
    refine h.congr ?_
    filter_upwards with x
    have := hK_pt x
    linarith
  -- The difference of the goal equals the integral of K
  have hgoal_eq : (∫ x, f x ∂ν - ∫ x, f x ∂μ) - ∫ x, f x * L x ∂μ -
      (klDiv μ ν).toReal = ∫ x, K x ∂lam := by
    have hexp : (∫ x, f x ∂ν - ∫ x, f x ∂μ) - ∫ x, f x * L x ∂μ - (klDiv μ ν).toReal =
        (∫ x, pν x * f x ∂lam - ∫ x, pμ x * f x ∂lam) - ∫ x, pμ x * (f x * L x) ∂lam -
          ∫ x, pμ x * L' x ∂lam := by
      rw [hint_ν f, hint_μ f, hint_μ (fun x => f x * L x), hkl_int]
    rw [hexp]
    rw [← integral_sub hint_pνf hint_pμf]
    rw [← integral_sub hFG_int hint_pμfL]
    rw [← integral_sub hFGH_int hint_pμL']
    have h1 : ∫ x, ((((pν x * f x - pμ x * f x) - pμ x * (f x * L x)) - pμ x * L' x) - K x) ∂lam = 0 := by
      rw [show (fun x => ((((pν x * f x - pμ x * f x) - pμ x * (f x * L x)) - pμ x * L' x) - K x)) =
          fun x => pν x - pμ x from funext hK_pt]
      rw [integral_sub hpνi hpμi, hpν1, hpμ1, sub_self]
    have h2 : ∫ x, ((((pν x * f x - pμ x * f x) - pμ x * (f x * L x)) - pμ x * L' x) - K x) ∂lam =
        ∫ x, (((pν x * f x - pμ x * f x) - pμ x * (f x * L x)) - pμ x * L' x) ∂lam - ∫ x, K x ∂lam :=
      integral_sub hFGHH_int hK_int
    linarith
  -- Conclude
  have hmain : (∫ x, f x ∂ν - ∫ x, f x ∂μ) -
      ((∫ x, f x * L x ∂μ) + (klDiv μ ν).toReal) ≤ 0 := by
    have h1 : (∫ x, f x ∂ν - ∫ x, f x ∂μ) -
        ((∫ x, f x * L x ∂μ) + (klDiv μ ν).toReal) =
        (∫ x, f x ∂ν - ∫ x, f x ∂μ) - ∫ x, f x * L x ∂μ - (klDiv μ ν).toReal := by ring
    rw [h1, hgoal_eq]
    exact integral_nonpos hK_nonpos
  linarith
