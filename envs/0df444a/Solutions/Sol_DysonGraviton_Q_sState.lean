-- Prove2me | solution 1 for DysonGraviton.Q_sState
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T03:52:58.25778+00:00
-- url     : https://prove2.me/submissions/a75fa5a8-f1f2-4acc-85ef-bef13f88fc24

import Definitions.Def_DysonGraviton_Defs
import Mathlib

open MeasureTheory Filter Topology
open DysonGraviton

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem W6_DysonGraviton_cos_pos_iff (θ : ℝ) (h1 : -Real.pi < θ) (h2 : θ < Real.pi) :
    0 < Real.cos θ ↔ θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  constructor
  · intro hc
    by_contra hn
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hn
    rcases hn with hn | hn
    · have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -θ) (by linarith) (by linarith)
      rw [Real.cos_neg] at this
      linarith
    · have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := θ) hn (by linarith)
      linarith
  · exact Real.cos_pos_of_mem_Ioo

theorem W6_DysonGraviton_polar (g : ℝ × ℝ → ℝ) :
    ∫ p in halfPlane, g p = ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      q.1 * g (q.1 * Real.cos q.2, q.1 * Real.sin q.2) := by
  have hH : MeasurableSet halfPlane := measurableSet_Ioi.prod MeasurableSet.univ
  have hS' : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hT : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := rfl
  have hsub : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    rw [hT]
    refine ⟨hr, ?_, ?_⟩
    · linarith [hθ.1, Real.pi_pos]
    · linarith [hθ.2, Real.pi_pos]
  rw [← integral_indicator hH, ← integral_comp_polarCoord_symm]
  calc ∫ q in polarCoord.target, q.1 • halfPlane.indicator g (polarCoord.symm q)
      = ∫ q in polarCoord.target, (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)).indicator
          (fun q => q.1 * g (q.1 * Real.cos q.2, q.1 * Real.sin q.2)) q := by
        refine setIntegral_congr_fun polarCoord.open_target.measurableSet (fun q hq => ?_)
        classical
        obtain ⟨r, θ⟩ := q
        rw [hT] at hq
        obtain ⟨hr, hθ1, hθ2⟩ := hq
        have hr' : (0 : ℝ) < r := hr
        have hsymm : polarCoord.symm (r, θ) = (r * Real.cos θ, r * Real.sin θ) := rfl
        rw [hsymm, Set.indicator_apply, Set.indicator_apply, smul_eq_mul]
        have hmemH : ((r * Real.cos θ, r * Real.sin θ) ∈ halfPlane) ↔ 0 < r * Real.cos θ := by
          simp [halfPlane]
        have hiff := W6_DysonGraviton_cos_pos_iff θ hθ1 hθ2
        by_cases hc : 0 < Real.cos θ
        · have h1 : (r * Real.cos θ, r * Real.sin θ) ∈ halfPlane := hmemH.2 (mul_pos hr' hc)
          have h2 : ((r, θ) : ℝ × ℝ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
            ⟨hr', hiff.1 hc⟩
          rw [if_pos h1, if_pos h2]
        · have h1 : (r * Real.cos θ, r * Real.sin θ) ∉ halfPlane := by
            rw [hmemH]; intro h; exact hc (pos_of_mul_pos_right h hr'.le)
          have h2 : ((r, θ) : ℝ × ℝ) ∉ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
            rintro ⟨-, h⟩; exact hc (hiff.2 h)
          rw [if_neg h1, if_neg h2, mul_zero]
    _ = _ := by
        rw [setIntegral_indicator hS', Set.inter_eq_right.2 hsub]

theorem W6_DysonGraviton_dS (n R : ℝ) (hR : 0 < R) (s z : ℝ) (hs : 0 < s) :
    dS (sState n R) s z =
      -(s / Real.sqrt (s ^ 2 + z ^ 2)) *
        (n * Real.sqrt (s ^ 2 + z ^ 2) ^ (-n - 1) + Real.sqrt (s ^ 2 + z ^ 2) ^ (-n) / R) *
        Real.exp (-(Real.sqrt (s ^ 2 + z ^ 2)) / R) := by
  have hpos : 0 < s ^ 2 + z ^ 2 := by positivity
  have hρ0 : 0 < Real.sqrt (s ^ 2 + z ^ 2) := Real.sqrt_pos.2 hpos
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + z ^ 2) (2 * s) s := by
    have := ((hasDerivAt_id s).pow 2).add_const (z ^ 2)
    exact this.congr_deriv (by simp)
  have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + z ^ 2)) (s / Real.sqrt (s ^ 2 + z ^ 2)) s :=
    (h1.sqrt hpos.ne').congr_deriv (by field_simp)
  have h3 := h2.rpow_const (p := -n) (Or.inl hρ0.ne')
  have h2' : HasDerivAt (fun t : ℝ => -Real.sqrt (t ^ 2 + z ^ 2))
      (-(s / Real.sqrt (s ^ 2 + z ^ 2))) s := h2.neg
  have h4 := (h2'.div_const R).exp
  have h5 := h3.mul h4
  unfold dS sState
  refine h5.deriv.trans ?_
  ring

theorem W6_DysonGraviton_rho (r θ : ℝ) (hr : 0 < r) :
    Real.sqrt ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) = r := by
  rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one, Real.sqrt_sq hr.le]

theorem W6_DysonGraviton_exp_sq (r R : ℝ) :
    Real.exp (-r / R) ^ 2 = Real.exp (-(2 / R * r)) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

theorem W6_DysonGraviton_pw (t n : ℝ) (ht : 0 < t) (k : ℕ) :
    t ^ (((k : ℝ) + 1 - 2 * n) - 1) = t ^ k * (t ^ (-n)) ^ 2 := by
  rw [show ((k : ℝ) + 1 - 2 * n) - 1 = (k : ℝ) + (-n) + (-n) by ring,
    Real.rpow_add ht, Real.rpow_add ht, Real.rpow_natCast]
  ring

theorem W6_DysonGraviton_G (n R : ℝ) (hR : 0 < R) (k : ℕ) (hk : 0 < (k : ℝ) + 1 - 2 * n) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ k * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t)) =
      (R / 2) ^ ((k : ℝ) + 1 - 2 * n) * Real.Gamma ((k : ℝ) + 1 - 2 * n) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hk (by positivity : (0 : ℝ) < 2 / R)
  rw [show (1 : ℝ) / (2 / R) = R / 2 by field_simp] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [W6_DysonGraviton_pw t n ht k]

theorem W6_DysonGraviton_Gint (n R : ℝ) (hR : 0 < R) (k : ℕ) (hk : -1 < (k : ℝ) - 2 * n) :
    IntegrableOn (fun t : ℝ => t ^ k * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow hk one_pos (by positivity : (0 : ℝ) < 2 / R)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  try simp only []
  rw [Real.rpow_one, neg_mul]
  congr 1
  have := W6_DysonGraviton_pw t n ht' k
  rw [show ((k : ℝ) + 1 - 2 * n) - 1 = (k : ℝ) - 2 * n by ring] at this
  exact this

theorem W6_DysonGraviton_cos_int :
    ∫ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), Real.cos θ = 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_cos, Real.sin_neg, Real.sin_pi_div_two]
  norm_num

theorem W6_DysonGraviton_cos3_ii :
    ∫ x in (-(Real.pi / 2))..(Real.pi / 2), Real.cos x ^ 3 = 4 / 3 := by
  have hc : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have hc' : Real.cos (-(Real.pi / 2)) = 0 := by rw [Real.cos_neg, Real.cos_pi_div_two]
  have e : ∫ x in (-(Real.pi / 2))..(Real.pi / 2), Real.cos x ^ 3 =
      (Real.cos (Real.pi / 2) ^ (1 + 1) * Real.sin (Real.pi / 2) -
        Real.cos (-(Real.pi / 2)) ^ (1 + 1) * Real.sin (-(Real.pi / 2))) / ((1 : ℕ) + 2) +
        ((1 : ℕ) + 1) / ((1 : ℕ) + 2) * ∫ x in (-(Real.pi / 2))..(Real.pi / 2), Real.cos x ^ 1 :=
    integral_cos_pow 1
  rw [hc, hc'] at e
  rw [e]
  simp only [pow_one, integral_cos, Real.sin_neg, Real.sin_pi_div_two]
  norm_num

theorem W6_DysonGraviton_cos5_int :
    ∫ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), Real.cos θ ^ 5 = 16 / 15 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hc : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have hc' : Real.cos (-(Real.pi / 2)) = 0 := by rw [Real.cos_neg, Real.cos_pi_div_two]
  have e : ∫ x in (-(Real.pi / 2))..(Real.pi / 2), Real.cos x ^ 5 =
      (Real.cos (Real.pi / 2) ^ (3 + 1) * Real.sin (Real.pi / 2) -
        Real.cos (-(Real.pi / 2)) ^ (3 + 1) * Real.sin (-(Real.pi / 2))) / ((3 : ℕ) + 2) +
        ((3 : ℕ) + 1) / ((3 : ℕ) + 2) * ∫ x in (-(Real.pi / 2))..(Real.pi / 2), Real.cos x ^ 3 :=
    integral_cos_pow 3
  rw [hc, hc', W6_DysonGraviton_cos3_ii] at e
  rw [e]
  norm_num

theorem solution (n R : ℝ) (hR : 0 < R) (hn : n < 3 / 2) :
    Q (sState n R) = 4 / 5 * (1 - n / 6) := by
  have hpi := Real.pi_pos
  set a : ℝ := 3 - 2 * n with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set E : ℝ → ℝ := fun t => Real.exp (-(2 / R * t)) with hE
  set w : ℝ → ℝ := fun t => t ^ (-n) with hw
  -- radial integrals
  have hG2 := W6_DysonGraviton_G n R hR 2 (by push_cast; linarith)
  have hG3 := W6_DysonGraviton_G n R hR 3 (by push_cast; linarith)
  have hG4 := W6_DysonGraviton_G n R hR 4 (by push_cast; linarith)
  have hI2 := W6_DysonGraviton_Gint n R hR 2 (by push_cast; linarith)
  have hI3 := W6_DysonGraviton_Gint n R hR 3 (by push_cast; linarith)
  have hI4 := W6_DysonGraviton_Gint n R hR 4 (by push_cast; linarith)
  have e2 : ((2 : ℕ) : ℝ) + 1 - 2 * n = a := by rw [ha]; push_cast; ring
  have e3 : ((3 : ℕ) : ℝ) + 1 - 2 * n = a + 1 := by rw [ha]; push_cast; ring
  have e4 : ((4 : ℕ) : ℝ) + 1 - 2 * n = (a + 1) + 1 := by rw [ha]; push_cast; ring
  rw [e2] at hG2
  rw [e3] at hG3
  rw [e4] at hG4
  have hK : 0 < R / 2 := by positivity
  have hGa := Real.Gamma_pos_of_pos ha0
  have hKa : 0 < (R / 2) ^ a := Real.rpow_pos_of_pos hK a
  rw [Real.rpow_add_one hK.ne', Real.Gamma_add_one ha0.ne'] at hG3
  rw [Real.rpow_add_one hK.ne', Real.rpow_add_one hK.ne', Real.Gamma_add_one (by linarith),
    Real.Gamma_add_one ha0.ne'] at hG4
  -- the denominator
  have hden : denQ (sState n R) = ((R / 2) ^ a * Real.Gamma a) * 2 := by
    unfold denQ
    rw [W6_DysonGraviton_polar]
    rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      (g := fun q : ℝ × ℝ => (q.1 ^ 2 * (q.1 ^ (-n)) ^ 2 * Real.exp (-(2 / R * q.1))) * Real.cos q.2)
      (fun q hq => ?_)]
    · rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun t : ℝ => t ^ 2 * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t)))
        Real.cos, hG2, W6_DysonGraviton_cos_int]
    · obtain ⟨r, θ⟩ := q
      obtain ⟨hr, -⟩ := hq
      have hr' : (0 : ℝ) < r := hr
      simp only [sState]
      rw [W6_DysonGraviton_rho r θ hr', mul_pow, W6_DysonGraviton_exp_sq]
      ring
  -- the numerator
  have hnum : numQ (sState n R) = (n ^ 2 * ((R / 2) ^ a * Real.Gamma a) +
      2 * n / R * ((R / 2) ^ a * (R / 2) * (a * Real.Gamma a)) +
      1 / R ^ 2 * ((R / 2) ^ a * (R / 2) * (R / 2) * ((a + 1) * (a * Real.Gamma a)))) * (16 / 15) := by
    unfold numQ
    rw [W6_DysonGraviton_polar]
    rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      (g := fun q : ℝ × ℝ => (n ^ 2 * (q.1 ^ 2 * (q.1 ^ (-n)) ^ 2 * Real.exp (-(2 / R * q.1))) +
        2 * n / R * (q.1 ^ 3 * (q.1 ^ (-n)) ^ 2 * Real.exp (-(2 / R * q.1))) +
        1 / R ^ 2 * (q.1 ^ 4 * (q.1 ^ (-n)) ^ 2 * Real.exp (-(2 / R * q.1)))) * Real.cos q.2 ^ 5)
      (fun q hq => ?_)]
    · rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun t : ℝ => n ^ 2 * (t ^ 2 * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t))) +
        2 * n / R * (t ^ 3 * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t))) +
        1 / R ^ 2 * (t ^ 4 * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t)))) (fun θ => Real.cos θ ^ 5),
        W6_DysonGraviton_cos5_int]
      congr 1
      have hA : IntegrableOn (fun t : ℝ => n ^ 2 * (t ^ 2 * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t))))
          (Set.Ioi 0) := hI2.const_mul _
      have hB : IntegrableOn (fun t : ℝ => 2 * n / R * (t ^ 3 * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t))))
          (Set.Ioi 0) := hI3.const_mul _
      have hC : IntegrableOn (fun t : ℝ => 1 / R ^ 2 * (t ^ 4 * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t))))
          (Set.Ioi 0) := hI4.const_mul _
      have hAB : IntegrableOn (fun t : ℝ => n ^ 2 * (t ^ 2 * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t))) +
          2 * n / R * (t ^ 3 * (t ^ (-n)) ^ 2 * Real.exp (-(2 / R * t)))) (Set.Ioi 0) := hA.add hB
      rw [integral_add hAB hC, integral_add hA hB,
        integral_const_mul, integral_const_mul, integral_const_mul, hG2, hG3, hG4]
    · obtain ⟨r, θ⟩ := q
      obtain ⟨hr, hθ⟩ := hq
      have hr' : (0 : ℝ) < r := hr
      have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
      simp only
      rw [W6_DysonGraviton_dS n R hR _ _ (mul_pos hr' hc), W6_DysonGraviton_rho r θ hr',
        Real.rpow_sub_one hr'.ne']
      have hE2 := W6_DysonGraviton_exp_sq r R
      have hrne : r ≠ 0 := hr'.ne'
      have hRne : R ≠ 0 := hR.ne'
      rw [show (-(r * Real.cos θ / r) * (n * (r ^ (-n) / r) + r ^ (-n) / R) * Real.exp (-r / R)) ^ 2 =
          (Real.cos θ) ^ 2 * (n * (r ^ (-n) / r) + r ^ (-n) / R) ^ 2 * Real.exp (-r / R) ^ 2 by
          field_simp, hE2]
      field_simp
      ring
  unfold Q
  rw [hnum, hden]
  have hGne : Real.Gamma a ≠ 0 := hGa.ne'
  have hKne : (R / 2) ^ a ≠ 0 := hKa.ne'
  field_simp
  rw [ha]
  ring
