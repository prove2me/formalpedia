-- Prove2me | solution 1 for EthierKurtz.gaussian_density_perturbation_quantile_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:42:08.871109+00:00
-- url     : https://prove2.me/submissions/a2412795-439b-44fa-a0b2-d9bacddef32f

import Mathlib.Tactic
import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_density_perturbation_normalization
import Theorems.Thm_EthierKurtz_tusnady_quantile_sandwich
import Theorems.Thm_EthierKurtz_gaussian_density_perturbation_tail_lower
import Theorems.Thm_EthierKurtz_gaussian_density_perturbation_tail_upper




open MeasureTheory Set ProbabilityTheory

namespace QSAux

local notation "Ncdf" => ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))

def Hyp (c0 ε0 A b : ℝ) (h : ℝ → ℝ) (K0 ε : ℝ) : Prop :=
  (0 : ℝ) < ε ∧ (0 : ℝ) < K0 ∧ (∀ (x : ℝ), (0 : ℝ) ≤ h x) ∧
    MeasureTheory.Integrable h MeasureTheory.MeasureSpace.volume ∧
    ∫ (x : ℝ), h x = (1 : ℝ) ∧
    (∀ (x : ℝ), |x| ≤ ε0 / ε →
      h x ≤ K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
        Real.exp (c0 * ε * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ∧
    (∀ (x : ℝ), |x| ≤ ε0 / ε →
      K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
        Real.exp (-(c0 * ε * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ≤ h x) ∧
    ∫ (x : ℝ) in (Set.Icc (-(ε0 / ε)) (ε0 / ε))ᶜ, h x ≤ A * Real.exp (-(b / ε ^ (2 : ℕ)))

lemma hyp_refl {c0 ε0 A b K0 ε : ℝ} {h : ℝ → ℝ} (H : Hyp c0 ε0 A b h K0 ε) :
    Hyp c0 ε0 A b (fun x => h (-x)) K0 ε := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
  refine ⟨h1, h2, fun x => h3 _, h4.comp_neg, ?_, ?_, ?_, ?_⟩
  · rw [integral_neg_eq_self (fun x => h x) volume]; exact h5
  · intro x hx
    have := h6 (-x) (by rwa [abs_neg])
    simpa [abs_neg, neg_sq] using this
  · intro x hx
    have := h7 (-x) (by rwa [abs_neg])
    simpa [abs_neg, neg_sq] using this
  · set S := (Set.Icc (-(ε0 / ε)) (ε0 / ε))ᶜ with hS
    have hSm : MeasurableSet S := measurableSet_Icc.compl
    have key : ∀ x, -x ∈ S ↔ x ∈ S := by
      intro x; simp only [hS, mem_compl_iff, mem_Icc]
      constructor <;> intro k1 k2 <;> apply k1 <;> constructor <;> linarith [k2.1, k2.2]
    have e : (fun x => S.indicator (fun x => h (-x)) x) = fun x => S.indicator h (-x) := by
      ext x; by_cases hx : x ∈ S
      · rw [indicator_of_mem hx, indicator_of_mem ((key x).2 hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun k => hx ((key x).1 k))]
    rw [← integral_indicator hSm, e, integral_neg_eq_self (fun x => S.indicator h x) volume,
      integral_indicator hSm]
    exact h8

lemma L_real {h : ℝ → ℝ} (hn : ∀ x, 0 ≤ h x) (hi : Integrable h) (a : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    (Measure.map (fun x : ℝ => a * x)
      (volume.withDensity fun x => ENNReal.ofReal (h x))).real S
      = ∫ x in (fun x : ℝ => a * x) ⁻¹' S, h x := by
  have hm : Measurable (fun x : ℝ => a * x) := by fun_prop
  rw [measureReal_def, Measure.map_apply hm hS, withDensity_apply _ (hm hS),
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (Filter.Eventually.of_forall hn),
    ENNReal.toReal_ofReal (setIntegral_nonneg (hm hS) fun x _ => hn x)]

lemma pre_Ioi {a : ℝ} (ha : 0 < a) (y : ℝ) : (fun x : ℝ => a * x) ⁻¹' Ioi y = Ioi (y / a) := by
  ext x; simp only [mem_preimage, mem_Ioi]; rw [div_lt_iff₀ ha, mul_comm]

lemma pre_Iio {a : ℝ} (ha : 0 < a) (y : ℝ) : (fun x : ℝ => a * x) ⁻¹' Iio y = Iio (y / a) := by
  ext x; simp only [mem_preimage, mem_Iio]; rw [lt_div_iff₀ ha, mul_comm]

lemma pre_Iic {a : ℝ} (ha : 0 < a) (z : ℝ) : (fun x : ℝ => a * x) ⁻¹' Iic (a * z) = Iic z := by
  ext x; simp only [mem_preimage, mem_Iic]; exact mul_le_mul_iff_right₀ ha

lemma gpdf_eq (x : ℝ) : gaussianPDFReal 0 1 x
    = (√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ))) := by
  simp [gaussianPDFReal, neg_div]

lemma Ncdf_eq (z : ℝ) : Ncdf z
    = ∫ x in Iic z, (√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ))) := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic fun _ _ => gaussianPDFReal_nonneg _ _ _)]
  simp only [gpdf_eq]

lemma phi_int : Integrable (fun x : ℝ => (√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) := by
  have := integrable_gaussianPDFReal 0 1
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  exact gpdf_eq x

lemma psi_nonneg (r : ℝ) : 0 ≤ 1 - Ncdf r := sub_nonneg.2 (cdf_le_one _ _)

lemma cube_eq {m y : ℝ} (hm : 0 < m) :
    1 / √m * (y / √m) ^ 3 = y ^ 3 / m ^ 2 := by
  have hs : 0 < √m := Real.sqrt_pos.2 hm
  have h2 : √m ^ 2 = m := Real.sq_sqrt hm.le
  field_simp
  rw [show √m ^ 4 = (√m ^ 2) ^ 2 by ring, h2]; ring

end QSAux

open QSAux in
theorem solution :
    ∀ {c0 ε0 A b : ℝ},
      (0 : ℝ) ≤ c0 →
        (0 : ℝ) < ε0 →
          c0 * ε0 ≤ (1 / 16 : ℝ) →
            (0 : ℝ) ≤ A →
              (0 : ℝ) < b →
                ∃ (c : ℝ) (εt : ℝ) (m₀ : ℕ),
                  (0 : ℝ) < c ∧
                    (0 : ℝ) < εt ∧
                      (1 : ℕ) ≤ m₀ ∧
                        ∀ (m : ℕ),
                          m₀ ≤ m →
                            ∀ (h : ℝ → ℝ) (K0 : ℝ),
                              (0 : ℝ) < (1 : ℝ) / √↑m ∧
                                  (0 : ℝ) < K0 ∧
                                    (∀ (x : ℝ), (0 : ℝ) ≤ h x) ∧
                                      MeasureTheory.Integrable h MeasureTheory.MeasureSpace.volume ∧
                                        ∫ (x : ℝ), h x = (1 : ℝ) ∧
                                          (∀ (x : ℝ),
                                              |x| ≤ ε0 / ((1 : ℝ) / √↑m) →
                                                h x ≤
                                                  K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                                    Real.exp (c0 * ((1 : ℝ) / √↑m) * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ∧
                                            (∀ (x : ℝ),
                                                |x| ≤ ε0 / ((1 : ℝ) / √↑m) →
                                                  K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                                      Real.exp (-(c0 * ((1 : ℝ) / √↑m) * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ≤
                                                    h x) ∧
                                              ∫ (x : ℝ) in (Set.Icc (-(ε0 / ((1 : ℝ) / √↑m))) (ε0 / ((1 : ℝ) / √↑m)))ᶜ,
                                                  h x ≤
                                                A * Real.exp (-(b / ((1 : ℝ) / √↑m) ^ (2 : ℕ))) →
                                ∀ (y : ℝ),
                                  |y| ≤ εt * ↑m →
                                    (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                          (y / √↑m) ≤
                                        (ProbabilityTheory.cdf
                                              (MeasureTheory.Measure.map (fun (x : ℝ) => √↑m * x)
                                                (MeasureTheory.Measure.withDensity MeasureTheory.MeasureSpace.volume
                                                  fun (x : ℝ) => ENNReal.ofReal (h x))))
                                          (y + c * ((1 : ℝ) + y ^ (2 : ℕ) / ↑m)) ∧
                                      (ProbabilityTheory.cdf
                                              (MeasureTheory.Measure.map (fun (x : ℝ) => √↑m * x)
                                                (MeasureTheory.Measure.withDensity MeasureTheory.MeasureSpace.volume
                                                  fun (x : ℝ) => ENNReal.ofReal (h x))))
                                          (y - c * ((1 : ℝ) + y ^ (2 : ℕ) / ↑m)) ≤
                                        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                          (y / √↑m) := by
  intro c0 ε0 A b hc0 hε0 hcε hA hb
  obtain ⟨C3, ε1, hC3, hε1, -, -, hN⟩ :=
    EthierKurtz.gaussian_density_perturbation_normalization hc0 hε0 hcε hA hb
  obtain ⟨cU, εU, hcU, hεU, hU⟩ :=
    EthierKurtz.gaussian_density_perturbation_tail_upper hc0 hε0 hcε hA hb
  obtain ⟨cLo, εLo, hcLo, hεLo, hLo⟩ :=
    EthierKurtz.gaussian_density_perturbation_tail_lower hc0 hε0 hcε hA hb
  set εs := min ε1 (min εU εLo) with hεs
  have hεs0 : 0 < εs := lt_min hε1 (lt_min hεU hεLo)
  set cR := max cU cLo with hcR
  have hcR0 : 0 < cR := lt_max_of_lt_left hcU
  set εR := min (√b) (ε0 / 2) with hεR
  have hεR0 : 0 < εR := lt_min (Real.sqrt_pos.2 hb) (by linarith)
  obtain ⟨c, εt, m₀', hc, hεt, hm₀', hT⟩ :=
    EthierKurtz.tusnady_quantile_sandwich cR εR cR εR C3 hcR0 hεR0 hcR0 hεR0 hC3
  refine ⟨c, εt, max m₀' (⌈1 / εs ^ 2⌉₊ + 1), hc, hεt, le_max_of_le_left hm₀', ?_⟩
  intro m hm h K0 hH y hy
  have hH0 : Hyp c0 ε0 A b h K0 (1 / √(m : ℝ)) := hH
  have hH1 := hyp_refl hH0
  have hmN : ⌈1 / εs ^ 2⌉₊ + 1 ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : (0 : ℝ) < m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast le_trans (Nat.le_add_left 1 _) hmN
    linarith
  have hsq : 0 < √(m : ℝ) := Real.sqrt_pos.2 hmpos
  have hεm : 1 / √(m : ℝ) ≤ εs := by
    have h1 : 1 / εs ^ 2 ≤ (m : ℝ) := by
      have := Nat.le_ceil (1 / εs ^ 2)
      have h2 : ((⌈1 / εs ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hmN
      push_cast at h2; linarith
    rw [div_le_iff₀ hsq]
    have h3 : 1 / εs ≤ √(m : ℝ) := by
      rw [show 1 / εs = √((1 / εs) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by rw [div_pow, one_pow]; exact h1)
    rw [div_le_iff₀ hεs0] at h3; linarith
  have hε1' : 1 / √(m : ℝ) ≤ ε1 := hεm.trans (min_le_left _ _)
  have hεU' : 1 / √(m : ℝ) ≤ εU := hεm.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεLo' : 1 / √(m : ℝ) ≤ εLo := hεm.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨-, -, hnn, hint, hone, -, -, -⟩ := hH0
  set L := Measure.map (fun x : ℝ => √(m : ℝ) * x)
    (volume.withDensity fun x => ENNReal.ofReal (h x)) with hL
  have : IsProbabilityMeasure L := by
    constructor
    have hm : Measurable (fun x : ℝ => √(m : ℝ) * x) := by fun_prop
    rw [hL, Measure.map_apply hm MeasurableSet.univ, preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn), hone,
      ENNReal.ofReal_one]
  -- range facts
  have range : ∀ y : ℝ, √(m : ℝ) ≤ y → y ≤ εR * m →
      1 ≤ y / √(m : ℝ) ∧ y / √(m : ℝ) ≤ √b / (1 / √(m : ℝ)) ∧
        y / √(m : ℝ) ≤ ε0 / 2 / (1 / √(m : ℝ)) := by
    intro y hy1 hy2
    have hmm : (m : ℝ) = √(m : ℝ) * √(m : ℝ) := (Real.mul_self_sqrt hmpos.le).symm
    have hs : y / √(m : ℝ) ≤ εR * √(m : ℝ) := by
      rw [div_le_iff₀ hsq]; nlinarith
    refine ⟨by rw [le_div_iff₀ hsq]; linarith, ?_, ?_⟩
    · rw [div_div_eq_mul_div, div_one]
      exact hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hsq.le)
    · rw [div_div_eq_mul_div, div_one]
      exact hs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hsq.le)
  refine hT m (le_trans (le_max_left _ _) hm) L ?_ ?_ ?_ y hy
  · intro y hy1 hy2
    obtain ⟨r1, r2, r3⟩ := range y hy1 hy2
    have hX : 0 ≤ y ^ 3 / (m : ℝ) ^ 2 := by
      have : 0 ≤ y := le_trans hsq.le hy1
      positivity
    have e : L.real (Ioi y) = ∫ x in Ioi (y / √(m : ℝ)), h x := by
      rw [hL, L_real hnn hint _ measurableSet_Ioi, pre_Ioi hsq]
    have up := hU h K0 (1 / √(m : ℝ)) hH hεU' (y / √(m : ℝ)) r1 r2
    have lo := hLo h K0 (1 / √(m : ℝ)) hH hεLo' (y / √(m : ℝ)) r1 r3
    rw [mul_assoc, cube_eq hmpos] at up
    rw [mul_assoc, cube_eq hmpos] at lo
    rw [e]
    constructor
    · refine up.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (psi_nonneg _))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    · refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (psi_nonneg _)) lo
      exact neg_le_neg (mul_le_mul_of_nonneg_right (le_max_right _ _) hX)
  · intro y hy1 hy2
    obtain ⟨r1, r2, r3⟩ := range y hy1 hy2
    have hX : 0 ≤ y ^ 3 / (m : ℝ) ^ 2 := by
      have : 0 ≤ y := le_trans hsq.le hy1
      positivity
    have e : L.real (Iio (-y)) = ∫ x in Ioi (y / √(m : ℝ)), h (-x) := by
      rw [hL, L_real hnn hint _ measurableSet_Iio, pre_Iio hsq, integral_comp_neg_Ioi,
        integral_Iic_eq_integral_Iio, neg_div]
    have up := hU (fun x => h (-x)) K0 (1 / √(m : ℝ)) hH1 hεU' (y / √(m : ℝ)) r1 r2
    have lo := hLo (fun x => h (-x)) K0 (1 / √(m : ℝ)) hH1 hεLo' (y / √(m : ℝ)) r1 r3
    rw [mul_assoc, cube_eq hmpos] at up
    rw [mul_assoc, cube_eq hmpos] at lo
    rw [e]
    constructor
    · refine up.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (psi_nonneg _))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    · refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (psi_nonneg _)) lo
      exact neg_le_neg (mul_le_mul_of_nonneg_right (le_max_right _ _) hX)
  · intro z _
    have hBE := (hN h K0 (1 / √(m : ℝ)) hH hε1').2.2
    have e : cdf L (√(m : ℝ) * z) = ∫ x in Iic z, h x := by
      rw [cdf_eq_real, hL, L_real hnn hint _ measurableSet_Iic, pre_Iic hsq]
    set φ := fun x : ℝ => (√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ))) with hφ
    have hd : |(∫ x in Iic z, h x) - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) z| ≤ C3 / √(m : ℝ) := by
      rw [Ncdf_eq, ← integral_sub hint.integrableOn phi_int.integrableOn]
      refine (abs_integral_le_integral_abs).trans ?_
      refine (setIntegral_le_integral (hint.sub phi_int).abs
        (Filter.Eventually.of_forall fun x => abs_nonneg _)).trans ?_
      rw [show C3 / √(m : ℝ) = C3 * (1 / √(m : ℝ)) by ring]
      exact hBE
    rw [e]
    constructor <;> linarith [(abs_le.1 hd).1, (abs_le.1 hd).2]
