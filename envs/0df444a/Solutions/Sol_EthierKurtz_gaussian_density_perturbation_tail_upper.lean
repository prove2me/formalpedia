-- Prove2me | solution 1 for EthierKurtz.gaussian_density_perturbation_tail_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:38:08.976828+00:00
-- url     : https://prove2.me/submissions/e285d668-8f9a-4e6a-8855-0b852f985c85

import Mathlib.Tactic
import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_density_perturbation_normalization
import Theorems.Thm_OAI_GaussianPropeller_Mills_inverse_mills_ratio_deriv_le_one

open MeasureTheory Set

namespace UpAux

noncomputable def T (r : ℝ) : ℝ := ∫ t in Set.Ioi r, Real.exp (-t^2/2)

lemma integrable_E : Integrable (fun t : ℝ => Real.exp (-t^2/2)) := by
  have := integrable_exp_neg_mul_sq (b := 1/2) (by norm_num)
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only; congr 1; ring

lemma T_pos (r : ℝ) : 0 < T r := by
  unfold T
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun t => (Real.exp_pos _).le)
    integrable_E.integrableOn]
  have : Function.support (fun t : ℝ => Real.exp (-t^2/2)) = univ := by
    ext t; simp [(Real.exp_pos _).ne']
  rw [this, univ_inter, Real.volume_Ioi]; simp

lemma psi_eq (r : ℝ) : 1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) r
    = (√(2 * Real.pi))⁻¹ * T r := by
  rw [ProbabilityTheory.cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, compl_Iic,
    measureReal_def, ProbabilityTheory.gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun _ _ =>
      ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)]
  unfold T
  rw [← integral_const_mul]
  congr 1; ext t
  simp [ProbabilityTheory.gaussianPDFReal]

lemma E_le {s : ℝ} (hs : 0 ≤ s) : Real.exp (-(s^2/2)) ≤ (s + 1) * T s := by
  have hM := OAI.GaussianPropeller.Mills.inverse_mills_ratio_deriv_le_one s
  have hT := T_pos s
  change (Real.exp (-s^2/2) / T s) * (Real.exp (-s^2/2) / T s - s) ≤ 1 at hM
  rw [show -(s^2/2) = -s^2/2 by ring]
  set H := Real.exp (-s^2/2) / T s with hH
  have hE : Real.exp (-s^2/2) = H * T s := by rw [hH]; field_simp
  rw [hE]
  apply mul_le_mul_of_nonneg_right _ hT.le
  by_contra hc; push Not at hc
  nlinarith

lemma expI {a : ℝ} (s : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x => Real.exp (-(a * (x - s)))) (Ioi s) ∧
      ∫ x in Ioi s, Real.exp (-(a * (x - s))) = 1 / a := by
  have e : (fun x => Real.exp (-(a * (x - s)))) = fun x => Real.exp (a * s) * Real.exp ((-a) * x) := by
    funext x; rw [← Real.exp_add]; ring_nf
  rw [e]
  refine ⟨(integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) s).const_mul _, ?_⟩
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha)]
  have : Real.exp (a * s) * Real.exp (-(a * s)) = 1 := by rw [← Real.exp_add]; simp
  field_simp
  linarith

lemma key {c0 ε0 ε s x : ℝ} (hs : 1 ≤ s) (hsx : s ≤ x) (hx : ε * x ≤ ε0) (hc0 : 0 ≤ c0)
    (hε : 0 < ε) (hcε : c0 * ε ≤ 1) (hc : c0 * ε0 ≤ 1 / 16) :
    Real.exp (-(x^2/2)) * (Real.exp (c0 * ε * (1 + |x|^3)) - 1) ≤
      3 * c0 * ε * (Real.exp (-(s^2/2)) * Real.exp (c0 * ε * s^3)) *
        (5 * s^3 * Real.exp (-(13/16 * s * (x - s))) + 1000 * Real.exp (-(5/16 * (x - s)))) := by
  have hx0 : 0 ≤ x := by linarith
  rw [abs_of_nonneg hx0]
  set t := x - s with ht_def
  have ht : 0 ≤ t := by linarith
  have hxst : x = s + t := by rw [ht_def]; ring
  set u := c0 * ε * (1 + x^3) with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hexpu : Real.exp u - 1 ≤ u * Real.exp u := by
    have h1 := Real.add_one_le_exp (-u)
    have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos u
    nlinarith
  have hεs : ε * s ≤ ε0 := by nlinarith
  have hεt : ε * t ≤ ε0 := by nlinarith
  have ha : c0 * (ε * s) ≤ 1/16 := le_trans (mul_le_mul_of_nonneg_left hεs hc0) hc
  have hb : c0 * (ε * t) ≤ 1/16 := le_trans (mul_le_mul_of_nonneg_left hεt hc0) hc
  have hu1 : u ≤ c0 * ε + c0 * ε * s^3 + 3/16 * s * t + 1/4 * t^2 := by
    have e : u = c0 * ε + c0 * ε * s^3 + 3 * (c0 * (ε * s)) * (s * t)
        + 3 * (c0 * (ε * s)) * t^2 + (c0 * (ε * t)) * t^2 := by rw [hu_def, hxst]; ring
    have h1 := mul_le_mul_of_nonneg_right ha (show 0 ≤ s * t by positivity)
    have h2 := mul_le_mul_of_nonneg_right ha (show 0 ≤ t^2 by positivity)
    have h3 := mul_le_mul_of_nonneg_right hb (show 0 ≤ t^2 by positivity)
    nlinarith
  have hpoly : 1 + x^3 ≤ 5 * s^3 + 4 * t^3 := by
    rw [hxst]
    have : 1 ≤ s^3 := one_le_pow₀ hs
    nlinarith [mul_nonneg (add_nonneg (by linarith : (0:ℝ) ≤ s) ht) (sq_nonneg (s - t))]
  have hP : 0 < Real.exp (-(s^2/2)) * Real.exp (c0 * ε * s^3) := by positivity
  set P := Real.exp (-(s^2/2)) * Real.exp (c0 * ε * s^3) with hP_def
  have hexp : Real.exp (-(x^2/2)) * Real.exp u ≤
      3 * P * Real.exp (-(13/16 * s * t)) := by
    have h1 : Real.exp (-(x^2/2)) * Real.exp u ≤
        Real.exp (c0 * ε) * P * Real.exp (-(13/16 * s * t)) := by
      rw [hP_def, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [hxst]; nlinarith [sq_nonneg t]
    have h2 : Real.exp (c0 * ε) ≤ 3 := by
      have := Real.exp_one_lt_d9
      have := Real.exp_le_exp.mpr hcε
      linarith
    calc _ ≤ _ := h1
      _ ≤ 3 * P * Real.exp (-(13/16 * s * t)) := by gcongr
  have hcube : t^3 ≤ 216 * Real.exp (t/2) := by
    have h1 : t/6 ≤ Real.exp (t/6) := by have := Real.add_one_le_exp (t/6); linarith
    have h2 : (t/6)^3 ≤ Real.exp (t/6)^3 := pow_le_pow_left₀ (by positivity) h1 3
    rw [← Real.exp_nat_mul] at h2
    have : (3:ℕ) * (t/6) = t/2 := by push_cast; ring
    rw [this] at h2
    nlinarith
  have hq : 4 * t^3 * Real.exp (-(13/16 * s * t)) ≤ 1000 * Real.exp (-(5/16 * t)) := by
    have e1 : Real.exp (-(13/16 * s * t)) ≤ Real.exp (-(13/16) * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have e2 : Real.exp (t/2) * Real.exp (-(13/16) * t) = Real.exp (-(5/16 * t)) := by
      rw [← Real.exp_add]; ring_nf
    calc 4 * t^3 * Real.exp (-(13/16 * s * t)) ≤ 4 * (216 * Real.exp (t/2)) * Real.exp (-(13/16) * t) := by
          gcongr
      _ = 864 * Real.exp (-(5/16 * t)) := by rw [← e2]; ring
      _ ≤ _ := by have := Real.exp_pos (-(5/16 * t)); linarith
  have hEx : 0 ≤ Real.exp (-(x^2/2)) := (Real.exp_pos _).le
  have hcεn : 0 ≤ c0 * ε := by positivity
  calc Real.exp (-(x^2/2)) * (Real.exp u - 1) ≤ Real.exp (-(x^2/2)) * (u * Real.exp u) :=
        mul_le_mul_of_nonneg_left hexpu hEx
    _ = u * (Real.exp (-(x^2/2)) * Real.exp u) := by ring
    _ ≤ (c0 * ε * (5 * s^3 + 4 * t^3)) * (3 * P * Real.exp (-(13/16 * s * t))) := by
        apply mul_le_mul _ hexp (by positivity) (by positivity)
        rw [hu_def]; exact mul_le_mul_of_nonneg_left hpoly hcεn
    _ = 3 * c0 * ε * P * (5 * s^3 * Real.exp (-(13/16 * s * t)) + 4 * t^3 * Real.exp (-(13/16 * s * t))) := by ring
    _ ≤ 3 * c0 * ε * P * (5 * s^3 * Real.exp (-(13/16 * s * t)) + 1000 * Real.exp (-(5/16 * t))) := by
        gcongr
    _ = _ := by ring

end UpAux


set_option profiler true in
set_option maxHeartbeats 1000000 in
theorem solution :
    ∀ {c0 ε0 A b : ℝ},
      (0 : ℝ) ≤ c0 →
        (0 : ℝ) < ε0 →
          c0 * ε0 ≤ (1 / 16 : ℝ) →
            (0 : ℝ) ≤ A →
              (0 : ℝ) < b →
                ∃ (cU : ℝ) (ε1 : ℝ),
                  (0 : ℝ) < cU ∧
                    (0 : ℝ) < ε1 ∧
                      ∀ (h : ℝ → ℝ) (K0 ε : ℝ),
                        (0 : ℝ) < ε ∧
                            (0 : ℝ) < K0 ∧
                              (∀ (x : ℝ), (0 : ℝ) ≤ h x) ∧
                                MeasureTheory.Integrable h MeasureTheory.MeasureSpace.volume ∧
                                  ∫ (x : ℝ), h x = (1 : ℝ) ∧
                                    (∀ (x : ℝ),
                                        |x| ≤ ε0 / ε →
                                          h x ≤
                                            K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                              Real.exp (c0 * ε * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ∧
                                      (∀ (x : ℝ),
                                          |x| ≤ ε0 / ε →
                                            K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                                Real.exp (-(c0 * ε * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ≤
                                              h x) ∧
                                        ∫ (x : ℝ) in (Set.Icc (-(ε0 / ε)) (ε0 / ε))ᶜ, h x ≤
                                          A * Real.exp (-(b / ε ^ (2 : ℕ))) →
                          ε ≤ ε1 →
                            ∀ (s : ℝ),
                              (1 : ℝ) ≤ s →
                                s ≤ √b / ε →
                                  ∫ (x : ℝ) in Set.Ioi s, h x ≤
                                    ((1 : ℝ) -
                                        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) s) *
                                      Real.exp (cU * ε * s ^ (3 : ℕ)) := by
  intro c0 ε0 A b hc0 hε0 hc hA hb
  obtain ⟨C3, ε1, hC3, hε1, hε11, hε1c, hN⟩ :=
    EthierKurtz.gaussian_density_perturbation_normalization hc0 hε0 hc hA hb
  set q := √((2:ℝ) * Real.pi) with hq_def
  have hq : 0 < q := by positivity
  set w := √b with hw_def
  have hw : 0 < w := Real.sqrt_pos.mpr hb
  have hww : w * w = b := Real.mul_self_sqrt hb.le
  set C4 := 4 * A * q / w with hC4_def
  have hC4 : 0 ≤ C4 := by positivity
  refine ⟨C3 + 20000 * c0 + c0 + C4 + 1, ε1, by positivity, hε1, ?_⟩
  rintro h K0 ε ⟨hε, hK0, hh0, hhi, hh1, hU, hL, hT⟩ hεε1 s hs1 hsb
  obtain ⟨hK1, -, -⟩ := hN h K0 ε ⟨hε, hK0, hh0, hhi, hh1, hU, hL, hT⟩ hεε1
  have hcε : c0 * ε ≤ 1 := by
    calc c0 * ε ≤ c0 * ε1 := mul_le_mul_of_nonneg_left hεε1 hc0
      _ = ε1 * c0 := mul_comm _ _
      _ ≤ 1 := hε1c
  have hs0 : 0 < s := by linarith
  have hΨ := UpAux.psi_eq s
  generalize (1 : ℝ) - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) s = Ψ at hΨ ⊢
  have hTs := UpAux.T_pos s
  have hΨ0 : 0 < Ψ := by rw [hΨ]; positivity
  have hEs : q⁻¹ * Real.exp (-(s^2/2)) ≤ 2 * s * Ψ := by
    have := UpAux.E_le hs0.le
    rw [hΨ]
    have h2 : (s + 1) * UpAux.T s ≤ 2 * s * UpAux.T s :=
      mul_le_mul_of_nonneg_right (by linarith) hTs.le
    calc q⁻¹ * Real.exp (-(s^2/2)) ≤ q⁻¹ * (2 * s * UpAux.T s) := by gcongr; linarith
      _ = _ := by ring
  set R := ε0 / ε with hR_def
  set I := Set.Icc (-R) R with hI_def
  have hI : MeasurableSet I := measurableSet_Icc
  have hsplit := integral_inter_add_sdiff (μ := volume) (f := h) hI (hhi.integrableOn (s := Set.Ioi s))
  -- tail
  have htail : ∫ x in Set.Ioi s \ I, h x ≤ A * Real.exp (-(b / ε^2)) := by
    refine le_trans (setIntegral_mono_set hhi.integrableOn (ae_of_all _ fun x => hh0 x) ?_) hT
    exact (show Set.Ioi s \ I ⊆ Iᶜ from fun x hx => hx.2).eventuallyLE
  have hsε : s * ε ≤ w := by rwa [le_div_iff₀ hε] at hsb
  have htail2 : A * Real.exp (-(b / ε^2)) ≤ C4 * ε * Ψ := by
    set Y := b / (2 * ε^2) with hY
    have hY0 : 0 < Y := by positivity
    have e0 : Real.exp (-(b / ε^2)) = Real.exp (-Y) * Real.exp (-Y) := by
      rw [← Real.exp_add]; congr 1; rw [hY]; field_simp; ring
    have e1 : Real.exp (-Y) ≤ 2 * ε^2 / (w * w) := by
      rw [hww]
      have h1 : Real.exp (-Y) ≤ 1 / Y := by
        rw [le_div_iff₀ hY0]
        have h1 := Real.add_one_le_exp Y
        have h2 : Real.exp (-Y) * Real.exp Y = 1 := by rw [← Real.exp_add]; simp
        have h3 := Real.exp_pos (-Y)
        have h4 := mul_le_mul_of_nonneg_left h1 h3.le
        linarith
      calc Real.exp (-Y) ≤ 1 / Y := h1
        _ = 2 * ε^2 / b := by rw [hY]; field_simp
    have hs2 : s^2 / 2 ≤ Y := by
      rw [hY, le_div_iff₀ (by positivity)]
      have k := mul_le_mul hsε hsε (by positivity) hw.le
      calc s^2 / 2 * (2 * ε^2) = (s * ε) * (s * ε) := by ring
        _ ≤ w * w := k
        _ = b := hww
    have e2 : Real.exp (-Y) ≤ 2 * q * w * Ψ / ε := by
      have a1 : Real.exp (-Y) ≤ Real.exp (-(s^2/2)) := Real.exp_le_exp.mpr (by linarith)
      have a2 : Real.exp (-(s^2/2)) ≤ 2 * q * s * Ψ := by
        have := hEs; rw [inv_mul_le_iff₀ hq] at this; linarith
      have a3 : 2 * q * s * Ψ ≤ 2 * q * w * Ψ / ε := by
        rw [le_div_iff₀ hε]
        have := mul_le_mul_of_nonneg_left hsε (show 0 ≤ 2 * q * Ψ by positivity)
        calc 2 * q * s * Ψ * ε = 2 * q * Ψ * (s * ε) := by ring
          _ ≤ 2 * q * Ψ * w := this
          _ = 2 * q * w * Ψ := by ring
      linarith
    rw [e0]
    calc A * (Real.exp (-Y) * Real.exp (-Y)) ≤ A * ((2 * ε^2 / (w * w)) * (2 * q * w * Ψ / ε)) := by
          gcongr
      _ = C4 * ε * Ψ := by rw [hC4_def]; field_simp; ring
  -- main part
  set P := Real.exp (-(s^2/2)) * Real.exp (c0 * ε * s^3) with hP_def
  set G : ℝ → ℝ := fun x => 5 * s^3 * Real.exp (-(13/16 * s * (x - s))) +
    1000 * Real.exp (-(5/16 * (x - s))) with hG_def
  set F : ℝ → ℝ := fun x => K0 * (q⁻¹ * Real.exp (-x^2/2) + q⁻¹ * (3 * c0 * ε * P) * G x) with hF_def
  obtain ⟨i1, j1⟩ := UpAux.expI s (show (0:ℝ) < 13/16 * s by positivity)
  obtain ⟨i2, j2⟩ := UpAux.expI s (show (0:ℝ) < 5/16 by norm_num)
  have hGi : IntegrableOn G (Set.Ioi s) := (i1.const_mul (5 * s^3)).add (i2.const_mul 1000)
  have hGint : ∫ x in Set.Ioi s, G x = 5 * s^3 * (1 / (13/16 * s)) + 1000 * (1 / (5/16)) := by
    simp only [hG_def]
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul, j1, j2]
  have hGle : ∫ x in Set.Ioi s, G x ≤ 3207 * s^2 := by
    rw [hGint]
    have e1 : 5 * s^3 * (1 / (13/16 * s)) = 80/13 * s^2 := by field_simp; ring
    have e2 : (1000:ℝ) * (1 / (5/16)) = 3200 := by norm_num
    have : 1 ≤ s^2 := one_le_pow₀ hs1
    rw [e1, e2]; linarith
  have hGnn : 0 ≤ ∫ x in Set.Ioi s, G x := by
    rw [hGint]; positivity
  have hFi : IntegrableOn F (Set.Ioi s) :=
    (((UpAux.integrable_E.integrableOn (s := Set.Ioi s)).const_mul q⁻¹).add
      (hGi.const_mul (q⁻¹ * (3 * c0 * ε * P)))).const_mul K0
  have hFint : ∫ x in Set.Ioi s, F x =
      K0 * (q⁻¹ * UpAux.T s + q⁻¹ * (3 * c0 * ε * P) * ∫ x in Set.Ioi s, G x) := by
    simp only [hF_def]
    rw [integral_const_mul, integral_add ((UpAux.integrable_E.integrableOn).const_mul _)
      (hGi.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  have hpt : ∀ x ∈ Set.Ioi s ∩ I, h x ≤ F x := by
    rintro x ⟨hx1, hx2⟩
    have hx1' : s < x := hx1
    have hxR : |x| ≤ ε0 / ε := abs_le.mpr ⟨hx2.1, hx2.2⟩
    have hεx : ε * x ≤ ε0 := by
      have := hx2.2; rw [hR_def, le_div_iff₀ hε] at this; linarith
    have hk := UpAux.key hs1 hx1'.le hεx hc0 hε hcε hc
    rw [← hP_def] at hk
    have hu := hU x hxR
    simp only [hF_def, hG_def]
    rw [show -x^2/2 = -(x^2/2) by ring]
    have e : Real.exp (-(x^2/2)) * (Real.exp (c0 * ε * (1 + |x|^3)) - 1) =
        Real.exp (-(x^2/2)) * Real.exp (c0 * ε * (1 + |x|^3)) - Real.exp (-(x^2/2)) := by ring
    have h3 : Real.exp (-(x^2/2)) * Real.exp (c0 * ε * (1 + |x|^3)) ≤ Real.exp (-(x^2/2)) +
        3 * c0 * ε * P * (5 * s^3 * Real.exp (-(13/16 * s * (x - s))) +
          1000 * Real.exp (-(5/16 * (x - s)))) := by linarith
    calc h x ≤ K0 * (q⁻¹ * Real.exp (-(x^2/2))) * Real.exp (c0 * ε * (1 + |x|^3)) := hu
      _ = K0 * (q⁻¹ * (Real.exp (-(x^2/2)) * Real.exp (c0 * ε * (1 + |x|^3)))) := by ring
      _ ≤ K0 * (q⁻¹ * (Real.exp (-(x^2/2)) +
        3 * c0 * ε * P * (5 * s^3 * Real.exp (-(13/16 * s * (x - s))) +
          1000 * Real.exp (-(5/16 * (x - s)))))) := by gcongr
      _ = _ := by ring
  have hFnn : ∀ x, 0 ≤ F x := fun x => by simp only [hF_def, hG_def]; positivity
  have hmain : ∫ x in Set.Ioi s ∩ I, h x ≤ ∫ x in Set.Ioi s, F x := by
    calc ∫ x in Set.Ioi s ∩ I, h x ≤ ∫ x in Set.Ioi s ∩ I, F x :=
          setIntegral_mono_on hhi.integrableOn (hFi.mono_set Set.inter_subset_left)
            (measurableSet_Ioi.inter hI) hpt
      _ ≤ ∫ x in Set.Ioi s, F x :=
          setIntegral_mono_set hFi (ae_of_all _ fun x => hFnn x) Set.inter_subset_left.eventuallyLE
  set y := ε * s^3 with hy
  have hs3 : 1 ≤ s^3 := one_le_pow₀ hs1
  have hy0 : 0 ≤ y := by positivity
  have hy1 : ε ≤ y := le_mul_of_one_le_right hε.le hs3
  have hZ : Real.exp (c0 * ε * s^3) = Real.exp (c0 * y) := by rw [hy]; ring_nf
  have hFb : ∫ x in Set.Ioi s, F x ≤ K0 * (Ψ * (1 + 20000 * c0 * y * Real.exp (c0 * y))) := by
    rw [hFint]
    have a1 : q⁻¹ * P ≤ 2 * s * Ψ * Real.exp (c0 * y) := by
      rw [hP_def, ← mul_assoc, hZ]
      exact mul_le_mul_of_nonneg_right hEs (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ hK0.le
    rw [← hΨ]
    calc Ψ + q⁻¹ * (3 * c0 * ε * P) * ∫ x in Set.Ioi s, G x
        = Ψ + 3 * c0 * ε * (q⁻¹ * P) * ∫ x in Set.Ioi s, G x := by ring
      _ ≤ Ψ + 3 * c0 * ε * (2 * s * Ψ * Real.exp (c0 * y)) * (3207 * s^2) := by gcongr
      _ = Ψ * (1 + 19242 * c0 * y * Real.exp (c0 * y)) := by rw [hy]; ring
      _ ≤ Ψ * (1 + 20000 * c0 * y * Real.exp (c0 * y)) := by gcongr; norm_num
  have hK : K0 ≤ Real.exp (C3 * y) := by
    have h1 := (abs_le.mp hK1).2
    have h2 := Real.add_one_le_exp (C3 * y)
    have h3 : C3 * ε ≤ C3 * y := mul_le_mul_of_nonneg_left hy1 hC3.le
    linarith
  have hD : 1 + 20000 * c0 * y * Real.exp (c0 * y) ≤ Real.exp (20000 * c0 * y) * Real.exp (c0 * y) := by
    have e1 := Real.add_one_le_exp (20000 * c0 * y)
    have e2 : 1 ≤ Real.exp (c0 * y) := Real.one_le_exp (by positivity)
    have : 0 ≤ 20000 * c0 * y := by positivity
    have e3 := mul_le_mul_of_nonneg_right e1 (Real.exp_pos (c0 * y)).le
    linarith
  have hM : K0 * (1 + 20000 * c0 * y * Real.exp (c0 * y)) ≤ Real.exp ((C3 + 20000 * c0 + c0) * y) := by
    rw [show (C3 + 20000 * c0 + c0) * y = C3 * y + 20000 * c0 * y + c0 * y by ring, Real.exp_add,
      Real.exp_add]
    calc K0 * (1 + 20000 * c0 * y * Real.exp (c0 * y))
        ≤ Real.exp (C3 * y) * (Real.exp (20000 * c0 * y) * Real.exp (c0 * y)) :=
          mul_le_mul hK hD (by positivity) (by positivity)
      _ = _ := by ring
  have hfin : Real.exp ((C3 + 20000 * c0 + c0) * y) + C4 * y ≤
      Real.exp ((C3 + 20000 * c0 + c0 + C4 + 1) * y) := by
    have hM1 : 1 ≤ Real.exp ((C3 + 20000 * c0 + c0) * y) := Real.one_le_exp (by positivity)
    rw [show (C3 + 20000 * c0 + c0 + C4 + 1) * y = (C3 + 20000 * c0 + c0) * y + C4 * y + y by ring,
      Real.exp_add, Real.exp_add]
    have e1 := Real.add_one_le_exp (C4 * y)
    have e2 : 1 ≤ Real.exp y := Real.one_le_exp hy0
    have : 0 ≤ C4 * y := by positivity
    have e3 : Real.exp ((C3 + 20000 * c0 + c0) * y) * (C4 * y + 1) ≤
        Real.exp ((C3 + 20000 * c0 + c0) * y) * Real.exp (C4 * y) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have e4 : Real.exp ((C3 + 20000 * c0 + c0) * y) * Real.exp (C4 * y) * 1 ≤
        Real.exp ((C3 + 20000 * c0 + c0) * y) * Real.exp (C4 * y) * Real.exp y :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    have e5 : C4 * y * 1 ≤ C4 * y * Real.exp ((C3 + 20000 * c0 + c0) * y) :=
      mul_le_mul_of_nonneg_left hM1 this
    linarith
  rw [← hsplit, show (C3 + 20000 * c0 + c0 + C4 + 1) * ε * s ^ 3 = (C3 + 20000 * c0 + c0 + C4 + 1) * y by
    rw [hy]; ring]
  have f1 : K0 * (Ψ * (1 + 20000 * c0 * y * Real.exp (c0 * y))) ≤
      Ψ * Real.exp ((C3 + 20000 * c0 + c0) * y) := by
    rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hM hΨ0.le
  have f2 : C4 * ε * Ψ ≤ Ψ * (C4 * y) := by
    rw [mul_comm Ψ]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy1 hC4) hΨ0.le
  have f3 := mul_le_mul_of_nonneg_left hfin hΨ0.le
  rw [mul_add] at f3
  linarith
