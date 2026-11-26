-- Prove2me | solution 1 for GEPPGrowth.Main.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:40:23.322535+00:00
-- url     : https://prove2.me/submissions/ee7b7fba-09eb-474e-8e8a-29f65d6e60af

import Mathlib
import Definitions.Def_GEPPGrowth_Main_ChiSquare
import Theorems.Thm_DbarRegularity_lintegral_fun_norm_eq
import Theorems.Thm_PI_AprimeInfG_lintegral_fintype_prod

open MeasureTheory ProbabilityTheory WithLp
open scoped ENNReal

noncomputable section

namespace GEPPLemma48

open GEPPGrowth.Main

/-- Density of `N(0, I_k)` on `Fin k → ℝ`. -/
def gdens (k : ℕ) (x : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2) * Real.exp (-(∑ i, x i ^ 2) / 2))

lemma gauss_pi (k : ℕ) :
    Measure.pi (fun _ : Fin k => gaussianReal 0 1) = volume.withDensity (gdens k) := by
  have hg : ∀ x : Fin k → ℝ, gdens k x = ∏ i, gaussianPDF 0 1 (x i) := by
    intro x
    simp only [gdens, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    · rw [NNReal.coe_one, mul_one, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg_one,
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
      congr 1; ring
    · rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      simp [neg_div]
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (gdens k) =
      fun x => ∏ i, (s i).indicator (gaussianPDF 0 1) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx, hg x]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (Set.mem_univ _)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, volume_pi, PI.AprimeInfG.lintegral_fintype_prod (fun _ => (s _).indicator _)
    (fun i => (measurable_gaussianPDF 0 1).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply 0 one_ne_zero, lintegral_indicator (hs i)]

/-- The radial constant `k |B(0,1)| (2π)^{-k/2}`. -/
def Zk (k : ℕ) : ℝ≥0∞ :=
  k * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) *
    ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2))

/-- Polar coordinates for the chi-square law. -/
lemma lintegral_chiSquare (k : ℕ) (hk : 0 < k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂chiSquare k =
      Zk k * ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (r ^ (k - 1) * Real.exp (-r ^ 2 / 2)) * F (r ^ 2) := by
  set G : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2) * Real.exp (-r ^ 2 / 2)) * F (r ^ 2) with hGdef
  have hG : Measurable G :=
    (Measurable.ennreal_ofReal (by fun_prop)).mul (hF.comp (by fun_prop))
  have hgd : Measurable (gdens k) := by
    unfold gdens; exact Measurable.ennreal_ofReal (by fun_prop)
  rw [chiSquare, lintegral_map hF (by fun_prop), gauss_pi,
    lintegral_withDensity_eq_lintegral_mul _ hgd
      (show Measurable (fun a : Fin k → ℝ => F (∑ i, a i ^ 2)) from hF.comp (by fun_prop))]
  have h1 : (gdens k * fun a : Fin k → ℝ => F (∑ i, a i ^ 2)) = fun y => G ‖toLp 2 y‖ := by
    funext y
    have hn : ‖toLp 2 y‖ ^ 2 = ∑ i, y i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Pi.mul_apply, gdens, hGdef, hn]
  rw [h1]
  rw [show (∫⁻ a : Fin k → ℝ, (fun y => G ‖toLp 2 y‖) a) = ∫⁻ a : Fin k → ℝ, (G ∘ norm) (toLp 2 a)
    from rfl, (PiLp.volume_preserving_toLp (Fin k)).lintegral_comp (hG.comp measurable_norm)]
  change ∫⁻ x : EuclideanSpace ℝ (Fin k), G ‖x‖ = _
  rw [DbarRegularity.lintegral_fun_norm_eq hk G hG, Zk, mul_assoc (_ * _),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  simp only [hGdef]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  ring

/-- `∫_0^∞ r^q e^{-r²/2} dr = 2^{(q+1)/2 - 1} Γ((q+1)/2)` for `q > -1`. -/
lemma J_eq (q : ℝ) (hq : -1 < q) :
    ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (r ^ q * Real.exp (-r ^ 2 / 2)) =
      ENNReal.ofReal (2 ^ ((q + 1) / 2 - 1) * Real.Gamma ((q + 1) / 2)) := by
  have hfun : ∀ r ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ q * Real.exp (-r ^ 2 / 2)) =
      ENNReal.ofReal (r ^ q * Real.exp (-(1 / 2) * r ^ (2 : ℝ))) := by
    intro r _
    congr 2
    congr 1; rw [Real.rpow_two]; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hfun,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_rpow_mul_exp_neg_mul_rpow hq two_pos (by norm_num))
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr =>
        mul_nonneg (Real.rpow_nonneg (le_of_lt hr) _) (Real.exp_pos _).le)),
    integral_rpow_mul_exp_neg_mul_rpow two_pos hq (by norm_num)]
  congr 1
  rw [Real.rpow_sub_one two_ne_zero, one_div, Real.inv_rpow (by norm_num),
    show -(q + 1) / 2 = -((q + 1) / 2) by ring, Real.rpow_neg (by norm_num), inv_inv]
  ring

/-- `r^(k-1)` with a natural exponent, as a real power. -/
lemma pow_eq_rpow (k : ℕ) (hk : 0 < k) (r : ℝ) : r ^ (k - 1) = r ^ ((k : ℝ) - 1) := by
  rw [← Real.rpow_natCast, Nat.cast_sub hk]; simp

lemma Zk_eq (k : ℕ) (hk : 0 < k) :
    Zk k = ENNReal.ofReal (2 ^ ((k : ℝ) / 2 - 1) * Real.Gamma ((k : ℝ) / 2))⁻¹ := by
  have h := lintegral_chiSquare k hk (fun _ => 1) measurable_const
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [lintegral_const, measure_univ, mul_one] at h
  simp_rw [pow_eq_rpow k hk] at h
  rw [J_eq _ (by linarith), show ((k : ℝ) - 1 + 1) / 2 = (k : ℝ) / 2 by ring] at h
  have hpos : 0 < 2 ^ ((k : ℝ) / 2 - 1) * Real.Gamma ((k : ℝ) / 2) :=
    mul_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))
  rw [ENNReal.eq_inv_of_mul_eq_one_left h.symm, ← ENNReal.ofReal_inv_of_pos hpos]

lemma chiSquare_Iio (k : ℕ) : chiSquare k (Set.Iio 0) = 0 := by
  rw [chiSquare, Measure.map_apply (by fun_prop) measurableSet_Iio]
  convert measure_empty (μ := Measure.pi (fun _ : Fin k => gaussianReal 0 1))
  ext x
  simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
  positivity

/-- The `m`-th moment as a lower integral. -/
lemma lintegral_rpow (k : ℕ) (hk : 0 < k) (m : ℝ) (hm : -(k:ℝ)/2 < m) :
    ∫⁻ x, ENNReal.ofReal (x ^ m) ∂chiSquare k =
      ENNReal.ofReal (2 ^ m * Real.Gamma (m + (k:ℝ)/2) / Real.Gamma ((k:ℝ)/2)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [lintegral_chiSquare k hk _ (Measurable.ennreal_ofReal (by fun_prop)), Zk_eq k hk]
  have hfun : ∀ r ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ (k - 1) * Real.exp (-r ^ 2 / 2)) * ENNReal.ofReal ((r ^ 2) ^ m) =
      ENNReal.ofReal (r ^ ((k : ℝ) - 1 + 2 * m) * Real.exp (-r ^ 2 / 2)) := by
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    rw [← ENNReal.ofReal_mul (by positivity), pow_eq_rpow k hk, ← Real.rpow_natCast r 2,
      ← Real.rpow_mul hr'.le, Real.rpow_add hr']
    congr 1; push_cast; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hfun, J_eq _ (by linarith),
    ← ENNReal.ofReal_mul (by
      have : (0:ℝ) < (k:ℝ)/2 := by positivity
      have := Real.Gamma_pos_of_pos this
      positivity)]
  congr 1
  have e : ((k : ℝ) - 1 + 2 * m + 1) / 2 = m + (k : ℝ) / 2 := by ring
  rw [e]
  have hG : 0 < Real.Gamma ((k : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [show m + (k : ℝ) / 2 - 1 = m + ((k : ℝ) / 2 - 1) by ring, Real.rpow_add two_pos]
  have : (0:ℝ) < 2 ^ ((k : ℝ) / 2 - 1) := by positivity
  field_simp

end GEPPLemma48

open GEPPGrowth.Main GEPPLemma48 in
theorem solution (k : ℕ) (hk : 0 < k) (m : ℝ) (hm : -(k:ℝ)/2 < m) :
    Integrable (fun x : ℝ => Real.rpow x m) (chiSquare k) ∧
    (∫ x : ℝ, Real.rpow x m ∂(chiSquare k)) =
      Real.rpow 2 m * Real.Gamma (m + (k:ℝ)/2) / Real.Gamma ((k:ℝ)/2) := by
  have hnn : 0 ≤ᵐ[chiSquare k] fun x : ℝ => Real.rpow x m := by
    have : ∀ᵐ x ∂chiSquare k, x ∈ Set.Ici (0 : ℝ) := by
      rw [ae_iff]
      have h := chiSquare_Iio k
      rw [← Set.compl_Ici] at h
      exact h
    filter_upwards [this] with x hx
    exact Real.rpow_nonneg hx m
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.rpow x m) (chiSquare k) :=
    (Measurable.pow_const measurable_id m).aestronglyMeasurable
  have hL := lintegral_rpow k hk m hm
  refine ⟨⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩, ?_⟩
  · simp only [Real.rpow_eq_pow]; rw [hL]; exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
    simp only [Real.rpow_eq_pow] at hL ⊢
    rw [hL, ENNReal.toReal_ofReal]
    have : 0 < m + (k:ℝ)/2 := by linarith
    have : (0:ℝ) < (k:ℝ)/2 := by positivity
    have := Real.Gamma_pos_of_pos ‹0 < m + (k:ℝ)/2›
    have := Real.Gamma_pos_of_pos ‹(0:ℝ) < (k:ℝ)/2›
    positivity
