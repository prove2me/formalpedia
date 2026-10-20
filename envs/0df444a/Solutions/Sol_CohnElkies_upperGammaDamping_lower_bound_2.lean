-- Prove2me | solution 2 for CohnElkies.upperGammaDamping_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:34:56.764088+00:00
-- url     : https://prove2.me/submissions/cd0aad57-a113-4903-af6b-ace8bb85da70

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    (ℓ / (8 * Real.exp 1)) *
        min (T ^ 2 / η) |T| ≤
      upperGammaDamping ℓ η T := by
  unfold upperGammaDamping upperGammaDampingIntegrand
  -- pointwise facts on (0, ∞)
  have hdens : ∀ a : ℝ, 0 < a →
      0 < 1 - Real.exp (-(2 * a / ℓ)) ∧ 1 - Real.exp (-(2 * a / ℓ)) ≤ 2 * a / ℓ ∧
      a / (1 - Real.exp (-(2 * a / ℓ))) ≤ ℓ / 2 + a := by
    intro a ha'
    have hx : 0 < 2 * a / ℓ := by positivity
    have hE : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hden : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
    have hup : 1 - Real.exp (-(2 * a / ℓ)) ≤ 2 * a / ℓ := by
      have := Real.add_one_le_exp (-(2 * a / ℓ)); linarith
    have hbound : (2 * a / ℓ) / (1 + 2 * a / ℓ) ≤ 1 - Real.exp (-(2 * a / ℓ)) := by
      have h1 := Real.add_one_le_exp (2 * a / ℓ)
      have h2 : Real.exp (-(2 * a / ℓ)) = (Real.exp (2 * a / ℓ))⁻¹ := Real.exp_neg _
      rw [h2, div_le_iff₀ (by positivity)]
      have h3 := Real.exp_pos (2 * a / ℓ)
      have h4 : (Real.exp (2 * a / ℓ))⁻¹ * Real.exp (2 * a / ℓ) = 1 := inv_mul_cancel₀ h3.ne'
      nlinarith [mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr h3.le)]
    refine ⟨hden, hup, ?_⟩
    rw [div_le_iff₀ hden]
    have : (ℓ / 2 + a) * ((2 * a / ℓ) / (1 + 2 * a / ℓ)) = a := by field_simp <;> ring
    nlinarith [mul_le_mul_of_nonneg_left hbound (by positivity : (0:ℝ) ≤ ℓ / 2 + a)]
  set f : ℝ → ℝ := fun a => (1 - Real.cos (a * T)) * upperGammaMeasureDensity ℓ η a with hf
  have hfnn : ∀ a : ℝ, 0 < a → 0 ≤ f a := by
    intro a ha
    have := (hdens a ha).1
    have := Real.cos_le_one (a * T)
    simp only [hf, upperGammaMeasureDensity]
    have := Real.exp_pos (-η * a)
    apply mul_nonneg (by linarith); positivity
  -- integrability
  have hI1 : IntegrableOn (fun a : ℝ => (ℓ / 2) * Real.exp (-η * a)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hη).const_mul _
  have hI2' : IntegrableOn (fun a : ℝ => a * Real.exp (-η * a)) (Ioi 0) := by
    have := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := η) (by norm_num) one_pos hη)
    refine this.congr_fun (fun a ha => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
  have hg : IntegrableOn (fun a : ℝ => T ^ 2 / 2 * ((ℓ / 2) * Real.exp (-η * a) + a * Real.exp (-η * a)))
      (Ioi 0) := (hI1.add hI2').const_mul _
  have hfmeas : Measurable f := by
    simp only [hf, upperGammaMeasureDensity]; fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    refine Integrable.mono' hg hfmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have ha' : (0:ℝ) < a := ha
    obtain ⟨hden, -, hkey⟩ := hdens a ha'
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnn a ha')]
    have h1 := Real.one_sub_sq_div_two_le_cos (x := a * T)
    have he := Real.exp_pos (-η * a)
    simp only [hf, upperGammaMeasureDensity]
    have hd : 0 ≤ Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ)))) := by positivity
    calc (1 - Real.cos (a * T)) * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ)))))
        ≤ (a * T) ^ 2 / 2 * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ))))) :=
          mul_le_mul_of_nonneg_right (by linarith) hd
      _ = T ^ 2 / 2 * Real.exp (-η * a) * (a / (1 - Real.exp (-(2 * a / ℓ)))) := by
          field_simp
      _ ≤ T ^ 2 / 2 * Real.exp (-η * a) * (ℓ / 2 + a) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = _ := by ring
  rcases eq_or_ne T 0 with hT | hT
  · subst hT
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, abs_zero,
      min_self, mul_zero]
    exact setIntegral_nonneg measurableSet_Ioi (fun a ha => hfnn a ha)
  have hTpos : 0 < |T| := abs_pos.mpr hT
  set A : ℝ := min (1 / η) (1 / |T|) with hA
  have hApos : 0 < A := lt_min (by positivity) (by positivity)
  have hAη : η * A ≤ 1 := by
    have := min_le_left (1 / η) (1 / |T|); rw [← hA] at this
    calc η * A ≤ η * (1 / η) := mul_le_mul_of_nonneg_left this hη.le
      _ = 1 := by field_simp
  have hAT : |T| * A ≤ 1 := by
    have := min_le_right (1 / η) (1 / |T|); rw [← hA] at this
    calc |T| * A ≤ |T| * (1 / |T|) := mul_le_mul_of_nonneg_left this hTpos.le
      _ = 1 := by field_simp
  have hpt : ∀ a ∈ Ioc (0:ℝ) A, ℓ * T ^ 2 / (8 * Real.exp 1) ≤ f a := by
    intro a ha
    obtain ⟨ha0, haA⟩ := ha
    obtain ⟨hden, hup, -⟩ := hdens a ha0
    have hx : |a * T| ≤ 1 := by
      rw [abs_mul, abs_of_pos ha0]
      calc a * |T| ≤ A * |T| := mul_le_mul_of_nonneg_right haA hTpos.le
        _ ≤ 1 := by linarith
    have hc := Real.cos_bound hx
    have hcos : (a * T) ^ 2 / 4 ≤ 1 - Real.cos (a * T) := by
      have h4 : |a * T| ^ 4 ≤ |a * T| ^ 2 := by
        have h0 := abs_nonneg (a * T)
        have : |a * T| ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg (|a * T|)]
      have hsq : |a * T| ^ 2 = (a * T) ^ 2 := sq_abs _
      have := (abs_le.mp hc).2
      nlinarith
    have hexp : Real.exp (-1) ≤ Real.exp (-η * a) := by
      apply Real.exp_le_exp.mpr
      have : η * a ≤ η * A := mul_le_mul_of_nonneg_left haA hη.le
      linarith
    have he1 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    simp only [hf, upperGammaMeasureDensity]
    have hprod : a * (1 - Real.exp (-(2 * a / ℓ))) ≤ 2 * a ^ 2 / ℓ := by
      calc a * (1 - Real.exp (-(2 * a / ℓ))) ≤ a * (2 * a / ℓ) := mul_le_mul_of_nonneg_left hup ha0.le
        _ = 2 * a ^ 2 / ℓ := by ring
    have hdpos : 0 < a * (1 - Real.exp (-(2 * a / ℓ))) := by positivity
    have hd1 : Real.exp (-1) / (2 * a ^ 2 / ℓ) ≤
        Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ)))) :=
      div_le_div₀ (Real.exp_pos _).le hexp hdpos hprod
    calc ℓ * T ^ 2 / (8 * Real.exp 1) = (a * T) ^ 2 / 4 * (Real.exp (-1) / (2 * a ^ 2 / ℓ)) := by
          rw [he1]; field_simp <;> ring
      _ ≤ (1 - Real.cos (a * T)) * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ))))) :=
          mul_le_mul hcos hd1 (by positivity) (by nlinarith [Real.cos_le_one (a * T)])
  have hsub : Ioc (0:ℝ) A ⊆ Ioi 0 := Set.Ioc_subset_Ioi_self
  have hstep1 : (∫ a in Ioc (0:ℝ) A, f a) ≤ ∫ a in Ioi (0:ℝ), f a :=
    setIntegral_mono_set hfint
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha; exact hfnn a ha)
      (Filter.Eventually.of_forall hsub)
  have hstep2 : (∫ a in Ioc (0:ℝ) A, ℓ * T ^ 2 / (8 * Real.exp 1)) ≤ ∫ a in Ioc (0:ℝ) A, f a :=
    setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne)) (hfint.mono_set hsub) measurableSet_Ioc hpt
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hApos.le, sub_zero, smul_eq_mul] at hstep2
  have hmin : T ^ 2 * A = min (T ^ 2 / η) |T| := by
    rw [hA, mul_min_of_nonneg _ _ (sq_nonneg T)]
    congr 1
    · field_simp
    · rw [← sq_abs T]; field_simp
  calc ℓ / (8 * Real.exp 1) * min (T ^ 2 / η) |T| = A * (ℓ * T ^ 2 / (8 * Real.exp 1)) := by
        rw [← hmin]; ring
    _ ≤ _ := hstep2.trans hstep1

