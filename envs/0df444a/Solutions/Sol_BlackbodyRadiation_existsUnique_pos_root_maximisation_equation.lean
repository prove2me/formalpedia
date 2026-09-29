-- Prove2me | solution 1 for BlackbodyRadiation.existsUnique_pos_root_maximisation_equation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:34:43.63517+00:00
-- url     : https://prove2.me/submissions/8e22bbbd-bd27-47f6-88a0-041747f7f67c

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck
import Definitions.Def_BlackbodyRadiation_classical_limits

open MeasureTheory Filter Topology
open BlackbodyRadiation

theorem W2m_BlackbodyRadiation_planckWave_eq_jacobian_mul_planckFreq
    (h c kB T lam : ℝ) (hc : 0 < c) (hlam : 0 < lam) :
    planckWave h c kB T lam = c / lam ^ 2 * planckFreq h c kB T (c / lam) := by
  unfold planckWave planckFreq
  have hc' := hc.ne'
  have hl' := hlam.ne'
  have e : h * (c / lam) / (kB * T) = h * c / (lam * kB * T) := by ring
  have key : 2 * h * c ^ 2 / lam ^ 5 = c / lam ^ 2 * (2 * h * (c / lam) ^ 3 / c ^ 2) := by
    first | (field_simp; ring1) | field_simp
  rw [e, mul_div_assoc', ← key]

theorem W2m_BlackbodyRadiation_planckWave_eq_shape
    (h c kB T lam : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T)
    (hlam : 0 < lam) :
    planckWave h c kB T lam
      = 2 * kB ^ 5 * T ^ 5 / (h ^ 4 * c ^ 3) *
          planckShape 5 (h * c / (lam * kB * T)) := by
  unfold planckWave planckShape
  have hc' := hc.ne'
  have hl' := hlam.ne'
  have hh' := hh.ne'
  have hk' := hkB.ne'
  have hT' := hT.ne'
  have key : 2 * h * c ^ 2 / lam ^ 5
      = 2 * kB ^ 5 * T ^ 5 / (h ^ 4 * c ^ 3) * (h * c / (lam * kB * T)) ^ 5 := by
    first | (field_simp; ring1) | field_simp
  rw [mul_div_assoc', ← key]

theorem W2m_BlackbodyRadiation_planckShape_one_tendsto_one_nhdsWithin_zero :
    Filter.Tendsto (fun x : ℝ => planckShape 1 x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h1 := hasDerivAt_iff_tendsto_slope.1 (Real.hasDerivAt_exp 0)
  rw [Real.exp_zero] at h1
  have h2 : Tendsto (slope Real.exp 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    h1.mono_left (nhdsWithin_mono _ (fun x hx => (show (0 : ℝ) < x from hx).ne'))
  have h3 := h2.inv₀ one_ne_zero
  rw [inv_one] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [slope_def_field, planckShape, Real.exp_zero]

theorem W2m_BlackbodyRadiation_planckShape_zero_mul_exp_tendsto_one_atTop :
    Filter.Tendsto (fun x : ℝ => planckShape 0 x * Real.exp x) Filter.atTop (nhds 1) := by
  have h1 : Tendsto (fun x : ℝ => 1 - Real.exp (-x)) atTop (𝓝 1) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_sub 1
  have h2 := h1.inv₀ one_ne_zero
  rw [inv_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [planckShape, pow_zero]
  have hE : Real.exp x - 1 ≠ 0 :=
    (by linarith [Real.add_one_lt_exp hx.ne'] : (0 : ℝ) < Real.exp x - 1).ne'
  have hE0 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  rw [Real.exp_neg]
  first | (field_simp; ring1) | field_simp

theorem W2m_BlackbodyRadiation_planckFreq_div_rayleighJeansFreq_tendsto_one
    (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T) :
    Filter.Tendsto (fun ν : ℝ => planckFreq h c kB T ν / rayleighJeansFreq c kB T ν)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hy : Tendsto (fun ν : ℝ => h * ν / (kB * T)) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have H : Tendsto (fun ν : ℝ => h * ν / (kB * T)) (𝓝 0) (𝓝 (h * 0 / (kB * T))) := by
        apply Continuous.tendsto; fun_prop
      simpa using H.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ν hν
      exact div_pos (mul_pos hh hν) (mul_pos hkB hT)
  have H := W2m_BlackbodyRadiation_planckShape_one_tendsto_one_nhdsWithin_zero.comp hy
  refine H.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ν hν
  have hν0 : 0 < ν := hν
  have hpos : 0 < h * ν / (kB * T) := div_pos (mul_pos hh hν0) (mul_pos hkB hT)
  have hD : Real.exp (h * ν / (kB * T)) - 1 ≠ 0 :=
    (by linarith [Real.add_one_lt_exp hpos.ne'] :
      (0 : ℝ) < Real.exp (h * ν / (kB * T)) - 1).ne'
  have hc' := hc.ne'
  have hk' := hkB.ne'
  have hT' := hT.ne'
  have hn' := hν0.ne'
  simp only [Function.comp, planckShape, planckFreq, rayleighJeansFreq, pow_one]
  first | (field_simp; ring1) | field_simp

theorem W2m_BlackbodyRadiation_planckFreq_div_wienFreq_tendsto_one
    (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T) :
    Filter.Tendsto (fun ν : ℝ => planckFreq h c kB T ν / wienFreq h c kB T ν)
      Filter.atTop (nhds 1) := by
  have hy : Tendsto (fun ν : ℝ => h * ν / (kB * T)) atTop atTop :=
    (tendsto_id.const_mul_atTop hh).atTop_div_const (mul_pos hkB hT)
  have H := W2m_BlackbodyRadiation_planckShape_zero_mul_exp_tendsto_one_atTop.comp hy
  refine H.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ν hν0
  have hpos : 0 < h * ν / (kB * T) := div_pos (mul_pos hh hν0) (mul_pos hkB hT)
  have hD : Real.exp (h * ν / (kB * T)) - 1 ≠ 0 :=
    (by linarith [Real.add_one_lt_exp hpos.ne'] :
      (0 : ℝ) < Real.exp (h * ν / (kB * T)) - 1).ne'
  have hE0 : Real.exp (h * ν / (kB * T)) ≠ 0 := (Real.exp_pos _).ne'
  have hc' := hc.ne'
  have hk' := hkB.ne'
  have hT' := hT.ne'
  have hh' := hh.ne'
  have hn' := hν0.ne'
  simp only [Function.comp, planckShape, planckFreq, wienFreq, pow_zero, id]
  rw [Real.exp_neg]
  first | (field_simp; ring1) | field_simp

theorem W2m_BlackbodyRadiation_planckFreq_integrableOn_Ioi
    (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T) :
    IntegrableOn (fun ν : ℝ => planckFreq h c kB T ν) (Set.Ioi 0) volume := by
  set a := h / (kB * T) with ha_def
  have ha : 0 < a := by positivity
  have hmeas : Measurable (fun ν : ℝ => planckFreq h c kB T ν) := by
    unfold planckFreq; fun_prop
  have hexp : ∀ ν : ℝ, h * ν / (kB * T) = a * ν := fun ν => by rw [ha_def]; ring
  have hK : 0 < 2 * h / c ^ 2 := by positivity
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 2 * h / c ^ 2 / a) ?_
      hmeas.aestronglyMeasurable ?_
    · simp
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun ν hν => ?_
      have hν0 : 0 < ν := hν.1
      have hν1 : ν ≤ 1 := hν.2
      have hy : 0 < a * ν := mul_pos ha hν0
      have hE : a * ν ≤ Real.exp (a * ν) - 1 := by linarith [Real.add_one_le_exp (a * ν)]
      have hEpos : 0 < Real.exp (a * ν) - 1 := lt_of_lt_of_le hy hE
      show ‖planckFreq h c kB T ν‖ ≤ 2 * h / c ^ 2 / a
      unfold planckFreq
      rw [hexp ν, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) hEpos.le),
        div_le_iff₀ hEpos]
      have h3 : ν ^ 3 ≤ ν := by
        have h4 : ν ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h4 hν0.le]
      have ha' := ha.ne'
      calc 2 * h * ν ^ 3 / c ^ 2 = 2 * h / c ^ 2 * ν ^ 3 := by ring
        _ ≤ 2 * h / c ^ 2 * ν := mul_le_mul_of_nonneg_left h3 hK.le
        _ = 2 * h / c ^ 2 / a * (a * ν) := by first | (field_simp; ring1) | field_simp
        _ ≤ 2 * h / c ^ 2 / a * (Real.exp (a * ν) - 1) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
  · have hg : IntegrableOn (fun ν : ℝ => (2 * h / c ^ 2 * 5 ^ 5 / a ^ 5) * ν ^ (-2 : ℝ))
        (Set.Ioi 1) volume :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos) _
    refine Integrable.mono' hg hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun ν hν => ?_
    have hν1 : (1 : ℝ) < ν := hν
    have hν0 : 0 < ν := by linarith
    have hy : 0 < a * ν := mul_pos ha hν0
    have hE : (a * ν / 5) ^ 5 ≤ Real.exp (a * ν) - 1 := by
      have h1 : a * ν / 5 + 1 ≤ Real.exp (a * ν / 5) := Real.add_one_le_exp _
      have h2 : (a * ν / 5 + 1) ^ 5 ≤ Real.exp (a * ν / 5) ^ 5 :=
        pow_le_pow_left₀ (by positivity) h1 5
      rw [← Real.exp_nat_mul] at h2
      have h3 : ((5 : ℕ) : ℝ) * (a * ν / 5) = a * ν := by push_cast; ring
      rw [h3] at h2
      have hz : 0 ≤ a * ν / 5 := by positivity
      nlinarith [hz, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5]
    have hEpos : 0 < Real.exp (a * ν) - 1 := lt_of_lt_of_le (by positivity) hE
    show ‖planckFreq h c kB T ν‖ ≤ (2 * h / c ^ 2 * 5 ^ 5 / a ^ 5) * ν ^ (-2 : ℝ)
    unfold planckFreq
    rw [hexp ν, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) hEpos.le),
      div_le_iff₀ hEpos]
    have hrp : ν ^ (-2 : ℝ) = (ν ^ 2)⁻¹ := by
      rw [Real.rpow_neg hν0.le, Real.rpow_two]
    rw [hrp]
    have eq1 : 2 * h / c ^ 2 * 5 ^ 5 / a ^ 5 * (ν ^ 2)⁻¹ * (a * ν / 5) ^ 5
        = 2 * h * ν ^ 3 / c ^ 2 := by
      have := ha.ne'
      have := hν0.ne'
      have := hc.ne'
      first | (field_simp; ring1) | field_simp
    calc 2 * h * ν ^ 3 / c ^ 2
        = 2 * h / c ^ 2 * 5 ^ 5 / a ^ 5 * (ν ^ 2)⁻¹ * (a * ν / 5) ^ 5 := eq1.symm
      _ ≤ 2 * h / c ^ 2 * 5 ^ 5 / a ^ 5 * (ν ^ 2)⁻¹ * (Real.exp (a * ν) - 1) :=
        mul_le_mul_of_nonneg_left hE (by positivity)

theorem W2m_BlackbodyRadiation_rayleighJeansFreq_not_integrableOn_Ioi
    (c kB T : ℝ) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T) :
    ¬ IntegrableOn (fun ν : ℝ => rayleighJeansFreq c kB T ν) (Set.Ioi 0) volume := by
  intro hint
  have h1 : IntegrableOn (fun ν : ℝ => rayleighJeansFreq c kB T ν) (Set.Ioi 1) volume :=
    hint.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have h2 : IntegrableOn (fun _ : ℝ => 2 * kB * T / c ^ 2) (Set.Ioi 1) volume := by
    refine Integrable.mono' h1 aestronglyMeasurable_const ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun ν hν => ?_
    have hν1 : (1 : ℝ) < ν := hν
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    unfold rayleighJeansFreq
    have H : 1 ≤ ν ^ 2 := by nlinarith
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 H) (mul_pos hkB hT).le]
  have hC : (2 * kB * T / c ^ 2 : ℝ) ≠ 0 := by positivity
  rw [integrableOn_const_iff] at h2
  rcases h2 with h2 | h2
  · have : (2 * kB * T / c ^ 2 : ℝ) = 0 := by simpa using h2
    exact hC this
  · simp at h2

theorem W2m_BlackbodyRadiation_planck_interpolates_classical_laws
    (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T) :
    Filter.Tendsto (fun ν : ℝ => planckFreq h c kB T ν / rayleighJeansFreq c kB T ν)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
      Filter.Tendsto (fun ν : ℝ => planckFreq h c kB T ν / wienFreq h c kB T ν)
        Filter.atTop (nhds 1) ∧
      IntegrableOn (fun ν : ℝ => planckFreq h c kB T ν) (Set.Ioi 0) volume ∧
      ¬ IntegrableOn (fun ν : ℝ => rayleighJeansFreq c kB T ν) (Set.Ioi 0) volume :=
  ⟨W2m_BlackbodyRadiation_planckFreq_div_rayleighJeansFreq_tendsto_one h c kB T hh hc hkB hT,
    W2m_BlackbodyRadiation_planckFreq_div_wienFreq_tendsto_one h c kB T hh hc hkB hT,
    W2m_BlackbodyRadiation_planckFreq_integrableOn_Ioi h c kB T hh hc hkB hT,
    W2m_BlackbodyRadiation_rayleighJeansFreq_not_integrableOn_Ioi c kB T hc hkB hT⟩

theorem W2m_BlackbodyRadiation_concave_key (n : ℝ) (hn : 1 < n) (x y : ℝ) (hx : 0 < x)
    (hxy : x < y) (hxe : x = n * (1 - Real.exp (-x))) (hye : y = n * (1 - Real.exp (-y))) :
    False := by
  have hy : 0 < y := by linarith
  have hy' : y ≠ 0 := hy.ne'
  have hs0 : 0 < x / y := div_pos hx hy
  have hs1 : x / y < 1 := (div_lt_one hy).2 hxy
  have H := strictConvexOn_exp.2 (Set.mem_univ (-y)) (Set.mem_univ 0) (by linarith : -y ≠ 0)
    hs0 (by linarith : (0 : ℝ) < 1 - x / y) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at H
  have e : x / y * -y = -x := by rw [mul_neg, div_mul_cancel₀ x hy']
  rw [e] at H
  have hn0 : 0 < n := by linarith
  have hn' : n ≠ 0 := hn0.ne'
  have h1 : Real.exp (-x) = 1 - x / n := by
    rw [eq_sub_iff_add_eq, add_div' _ _ _ hn', div_eq_iff hn']; linarith
  have h2 : Real.exp (-y) = 1 - y / n := by
    rw [eq_sub_iff_add_eq, add_div' _ _ _ hn', div_eq_iff hn']; linarith
  rw [h1, h2] at H
  have e2 : x / y * (1 - y / n) + (1 - x / y) = 1 - x / n := by
    first | (field_simp; ring1) | field_simp
  linarith

theorem W2m_BlackbodyRadiation_existsUnique_pos_root_maximisation_equation
    (n : ℝ) (hn : 1 < n) :
    ∃! x : ℝ, 0 < x ∧ x = n * (1 - Real.exp (-x)) := by
  have hcont : Continuous (fun x : ℝ => n * (1 - Real.exp (-x)) - x) := by fun_prop
  set ε := (n - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hab : ε ≤ n := by rw [hε]; linarith
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ Set.Icc ε n, n * (1 - Real.exp (-x)) - x = 0 := by
    have H := intermediate_value_Icc' hab hcont.continuousOn
    have hmem : (0 : ℝ) ∈ Set.Icc (n * (1 - Real.exp (-n)) - n) (n * (1 - Real.exp (-ε)) - ε) := by
      constructor
      · have : 0 < n * Real.exp (-n) := mul_pos (by linarith) (Real.exp_pos _)
        nlinarith
      · have hE1 : 1 + ε ≤ Real.exp ε := by linarith [Real.add_one_le_exp ε]
        have hEE : Real.exp (-ε) * Real.exp ε = 1 := by rw [← Real.exp_add]; simp
        have hEpos : 0 < Real.exp (-ε) := Real.exp_pos _
        have hE : Real.exp (-ε) * (1 + ε) ≤ 1 := by
          nlinarith [mul_le_mul_of_nonneg_left hE1 hEpos.le]
        have hn2 : n = 2 * ε + 1 := by rw [hε]; ring
        rw [hn2]
        nlinarith [sq_nonneg ε, mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ 2 * ε + 1),
          (by linarith : (0 : ℝ) < 1 + ε)]
    obtain ⟨x, hx, hx0⟩ := H hmem
    exact ⟨x, hx, hx0⟩
  have hx0' : n * (1 - Real.exp (-x)) - x = 0 := hx0
  refine ⟨x, ⟨by linarith [hx.1], by linarith⟩, ?_⟩
  rintro y ⟨hy, hyeq⟩
  have hxe : x = n * (1 - Real.exp (-x)) := by linarith
  rcases lt_trichotomy y x with hlt | heq | hgt
  · exact (W2m_BlackbodyRadiation_concave_key n hn y x hy hlt hyeq hxe).elim
  · exact heq
  · exact (W2m_BlackbodyRadiation_concave_key n hn x y (by linarith [hx.1]) hgt hxe hyeq).elim

theorem W2m_BlackbodyRadiation_chord (u v : ℝ) (hu : 0 < u) (huv : u < v) :
    Real.exp (-u) < u / v * Real.exp (-v) + (1 - u / v) := by
  have hv : 0 < v := by linarith
  have hv' : v ≠ 0 := hv.ne'
  have hs0 : 0 < u / v := div_pos hu hv
  have hs1 : u / v < 1 := (div_lt_one hv).2 huv
  have H := strictConvexOn_exp.2 (Set.mem_univ (-v)) (Set.mem_univ 0) (by linarith : -v ≠ 0)
    hs0 (by linarith : (0 : ℝ) < 1 - u / v) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at H
  have e : u / v * -v = -u := by rw [mul_neg, div_mul_cancel₀ u hv']
  rw [e] at H
  exact H

theorem W2m_BlackbodyRadiation_shape_hasDerivAt (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (planckShape n)
      ((n * x ^ (n - 1) * (Real.exp x - 1) - x ^ n * Real.exp x) / (Real.exp x - 1) ^ 2) x := by
  have hE : Real.exp x - 1 ≠ 0 :=
    (by linarith [Real.add_one_lt_exp hx.ne'] : (0 : ℝ) < Real.exp x - 1).ne'
  have h1 := hasDerivAt_pow n x
  have h2 := (Real.hasDerivAt_exp x).sub_const 1
  have H := h1.fun_div h2 hE
  show HasDerivAt (fun y => y ^ n / (Real.exp y - 1)) _ x
  exact H

theorem W2m_BlackbodyRadiation_planckShape_lt_planckShape_of_root
    (n : ℕ) (hn : 2 ≤ n) (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hroot : x₀ = (n : ℝ) * (1 - Real.exp (-x₀))) :
    ∀ x : ℝ, 0 < x → x ≠ x₀ → planckShape n x < planckShape n x₀ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn' : (n : ℝ) ≠ 0 := hnR.ne'
  have he0 : Real.exp (-x₀) = 1 - x₀ / n := by
    rw [eq_sub_iff_add_eq, add_div' _ _ _ hn', div_eq_iff hn']; linarith
  have hpos : ∀ x, 0 < x → x < x₀ → x < n * (1 - Real.exp (-x)) := by
    intro x hx hxx
    have H := W2m_BlackbodyRadiation_chord x x₀ hx hxx
    rw [he0] at H
    have hx0' : x₀ ≠ 0 := hx₀.ne'
    have e2 : x / x₀ * (1 - x₀ / n) + (1 - x / x₀) = 1 - x / n := by
      first | (field_simp; ring1) | field_simp
    rw [e2] at H
    have H2 : x / n < 1 - Real.exp (-x) := by linarith
    rw [div_lt_iff₀ hnR] at H2
    linarith
  have hneg : ∀ x, x₀ < x → n * (1 - Real.exp (-x)) < x := by
    intro x hxx
    have hx : 0 < x := by linarith
    have hx' : x ≠ 0 := hx.ne'
    have H := W2m_BlackbodyRadiation_chord x₀ x hx₀ hxx
    rw [he0] at H
    have e3 : x₀ / x * (1 - x / n) = x₀ / x - x₀ / n := by
      first | (field_simp; ring1) | field_simp
    have H2 : x₀ / x * (1 - x / n) < x₀ / x * Real.exp (-x) := by rw [e3]; linarith
    have H3 : 1 - x / n < Real.exp (-x) := lt_of_mul_lt_mul_left H2 (by positivity)
    have H4 : 1 - Real.exp (-x) < x / n := by linarith
    rw [lt_div_iff₀ hnR] at H4
    linarith
  have hEe : ∀ x : ℝ, Real.exp x * Real.exp (-x) = 1 := by
    intro x; rw [← Real.exp_add]; simp
  have hnum : ∀ x : ℝ, 0 < x → (n : ℝ) * x ^ (n - 1) * (Real.exp x - 1) - x ^ n * Real.exp x
      = x ^ (n - 1) * (Real.exp x * ((n : ℝ) * (1 - Real.exp (-x)) - x)) := by
    intro x hx
    have hxn : x ^ n = x ^ (n - 1) * x := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hxn]
    linear_combination ((n : ℝ) * x ^ (n - 1)) * hEe x
  have hEpos : ∀ x : ℝ, 0 < x → 0 < Real.exp x - 1 := fun x hx => by
    linarith [Real.add_one_lt_exp hx.ne']
  have hmono : StrictMonoOn (planckShape n) (Set.Ioc 0 x₀) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc 0 x₀)
    · intro x hx
      exact (W2m_BlackbodyRadiation_shape_hasDerivAt n x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(W2m_BlackbodyRadiation_shape_hasDerivAt n x hx.1).deriv, hnum x hx.1]
      refine div_pos ?_ (pow_pos (hEpos x hx.1) 2)
      exact mul_pos (pow_pos hx.1 _)
        (mul_pos (Real.exp_pos x) (sub_pos.2 (hpos x hx.1 hx.2)))
  have hanti : StrictAntiOn (planckShape n) (Set.Ici x₀) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici x₀)
    · intro x hx
      exact (W2m_BlackbodyRadiation_shape_hasDerivAt n x
        (lt_of_lt_of_le hx₀ hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans hx₀ hx
      rw [(W2m_BlackbodyRadiation_shape_hasDerivAt n x hx0).deriv, hnum x hx0]
      refine div_neg_of_neg_of_pos ?_ (pow_pos (hEpos x hx0) 2)
      exact mul_neg_of_pos_of_neg (pow_pos hx0 _)
        (mul_neg_of_pos_of_neg (Real.exp_pos x) (sub_neg.2 (hneg x hx)))
  intro x hx hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hmono ⟨hx, h.le⟩ ⟨hx₀, le_refl _⟩ h
  · exact hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h.le) h

theorem W2m_BlackbodyRadiation_planckFreq_eq_shape
    (h c kB T ν : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T) :
    planckFreq h c kB T ν
      = 2 * kB ^ 3 * T ^ 3 / (h ^ 2 * c ^ 2) * planckShape 3 (h * ν / (kB * T)) := by
  unfold planckFreq planckShape
  have hc' := hc.ne'
  have hh' := hh.ne'
  have hk' := hkB.ne'
  have hT' := hT.ne'
  have key : 2 * h * ν ^ 3 / c ^ 2
      = 2 * kB ^ 3 * T ^ 3 / (h ^ 2 * c ^ 2) * (h * ν / (kB * T)) ^ 3 := by
    first | (field_simp; ring1) | field_simp
  rw [mul_div_assoc', ← key]

theorem W2m_BlackbodyRadiation_wien_displacement_law
    (h c kB : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) :
    ∃ b : ℝ, 0 < b ∧
      (∃ x : ℝ, 0 < x ∧ x = 5 * (1 - Real.exp (-x)) ∧ b = h * c / (x * kB)) ∧
      ∀ T : ℝ, 0 < T → ∀ lam : ℝ, 0 < lam → lam ≠ b / T →
        planckWave h c kB T lam < planckWave h c kB T (b / T) := by
  obtain ⟨x₀, ⟨hx₀, hroot⟩, -⟩ :=
    W2m_BlackbodyRadiation_existsUnique_pos_root_maximisation_equation 5 (by norm_num)
  refine ⟨h * c / (x₀ * kB), by positivity, ⟨x₀, hx₀, hroot, rfl⟩, ?_⟩
  intro T hT lam hlam hne
  have hb : 0 < h * c / (x₀ * kB) / T := by positivity
  rw [W2m_BlackbodyRadiation_planckWave_eq_shape h c kB T lam hh hc hkB hT hlam,
    W2m_BlackbodyRadiation_planckWave_eq_shape h c kB T _ hh hc hkB hT hb]
  have hx0' := hx₀.ne'
  have hc' := hc.ne'
  have hh' := hh.ne'
  have hk' := hkB.ne'
  have hT' := hT.ne'
  have e0 : h * c / (h * c / (x₀ * kB) / T * kB * T) = x₀ := by
    first | (field_simp; ring1) | field_simp
  rw [e0]
  refine mul_lt_mul_of_pos_left ?_ (by positivity)
  refine W2m_BlackbodyRadiation_planckShape_lt_planckShape_of_root 5 (by norm_num) x₀ hx₀
    (by push_cast; exact hroot) _ (by positivity) ?_
  intro heq
  apply hne
  rw [div_eq_iff (by positivity)] at heq
  rw [eq_div_iff hT', eq_div_iff (by positivity)]
  linarith

theorem W2m_BlackbodyRadiation_wien_displacement_law_frequency
    (h c kB : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) :
    ∃ a : ℝ, 0 < a ∧
      (∃ x : ℝ, 0 < x ∧ x = 3 * (1 - Real.exp (-x)) ∧ a = x * kB / h) ∧
      ∀ T : ℝ, 0 < T → ∀ ν : ℝ, 0 < ν → ν ≠ a * T →
        planckFreq h c kB T ν < planckFreq h c kB T (a * T) := by
  obtain ⟨x₀, ⟨hx₀, hroot⟩, -⟩ :=
    W2m_BlackbodyRadiation_existsUnique_pos_root_maximisation_equation 3 (by norm_num)
  refine ⟨x₀ * kB / h, by positivity, ⟨x₀, hx₀, hroot, rfl⟩, ?_⟩
  intro T hT ν hν hne
  rw [W2m_BlackbodyRadiation_planckFreq_eq_shape h c kB T ν hh hc hkB hT,
    W2m_BlackbodyRadiation_planckFreq_eq_shape h c kB T _ hh hc hkB hT]
  have hx0' := hx₀.ne'
  have hh' := hh.ne'
  have hk' := hkB.ne'
  have hT' := hT.ne'
  have e0 : h * (x₀ * kB / h * T) / (kB * T) = x₀ := by
    first | (field_simp; ring1) | field_simp
  rw [e0]
  refine mul_lt_mul_of_pos_left ?_ (by positivity)
  refine W2m_BlackbodyRadiation_planckShape_lt_planckShape_of_root 3 (by norm_num) x₀ hx₀
    (by push_cast; exact hroot) _ (by positivity) ?_
  intro heq
  apply hne
  rw [div_eq_iff (by positivity)] at heq
  rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hh']
  linarith

theorem W2m_BlackbodyRadiation_root_sign (n : ℝ) (hnR : 0 < n) (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hroot : x₀ = n * (1 - Real.exp (-x₀))) :
    (∀ x, 0 < x → x < x₀ → x < n * (1 - Real.exp (-x))) ∧
      (∀ x, x₀ < x → n * (1 - Real.exp (-x)) < x) := by
  have hn' : n ≠ 0 := hnR.ne'
  have he0 : Real.exp (-x₀) = 1 - x₀ / n := by
    rw [eq_sub_iff_add_eq, add_div' _ _ _ hn', div_eq_iff hn']; linarith
  constructor
  · intro x hx hxx
    have H := W2m_BlackbodyRadiation_chord x x₀ hx hxx
    rw [he0] at H
    have hx0' : x₀ ≠ 0 := hx₀.ne'
    have e2 : x / x₀ * (1 - x₀ / n) + (1 - x / x₀) = 1 - x / n := by
      first | (field_simp; ring1) | field_simp
    rw [e2] at H
    have H2 : x / n < 1 - Real.exp (-x) := by linarith
    rw [div_lt_iff₀ hnR] at H2
    linarith
  · intro x hxx
    have hx : 0 < x := by linarith
    have hx' : x ≠ 0 := hx.ne'
    have H := W2m_BlackbodyRadiation_chord x₀ x hx₀ hxx
    rw [he0] at H
    have e3 : x₀ / x * (1 - x / n) = x₀ / x - x₀ / n := by
      first | (field_simp; ring1) | field_simp
    have H2 : x₀ / x * (1 - x / n) < x₀ / x * Real.exp (-x) := by rw [e3]; linarith
    have H3 : 1 - x / n < Real.exp (-x) := lt_of_mul_lt_mul_left H2 (by positivity)
    have H4 : 1 - Real.exp (-x) < x / n := by linarith
    rw [lt_div_iff₀ hnR] at H4
    linarith

theorem W2m_BlackbodyRadiation_root_maximisation_equation_five_numeric
    (x : ℝ) (hx : 0 < x) (hroot : x = 5 * (1 - Real.exp (-x))) :
    4.9651142317 < x ∧ x < 4.9651142318 := by
  obtain ⟨hE1, hE2⟩ := abs_le.1 Real.exp_one_near_20
  have hEpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hlo : (4.9651142317 : ℝ) < 5 * (1 - Real.exp (-4.9651142317)) := by
    have e1 : Real.exp (-4.9651142317) = Real.exp 0.0348857683 / Real.exp 1 ^ 5 := by
      rw [show (-4.9651142317 : ℝ) = 0.0348857683 - ((5 : ℕ) : ℝ) * 1 by norm_num,
        Real.exp_sub, Real.exp_nat_mul]
    rw [e1]
    obtain ⟨-, hX2⟩ := abs_le.1 (Real.exp_bound (x := (0.0348857683 : ℝ))
      (by rw [abs_of_pos (by norm_num)]; norm_num) (n := 7) (by norm_num))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.0348857683)] at hX2
    norm_num [Finset.sum_range_succ, Nat.factorial] at hX2
    have h5 : ((363916618873 : ℝ) / 133877442384 - 1 / 10 ^ 20) ^ 5 ≤ Real.exp 1 ^ 5 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 5
    have h5' := mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 1 - 4.9651142317 / 5)
    have key : Real.exp 0.0348857683 / Real.exp 1 ^ 5 < 1 - 4.9651142317 / 5 := by
      rw [div_lt_iff₀ (by positivity)]
      norm_num at h5' ⊢
      linarith
    linarith
  have hhi : 5 * (1 - Real.exp (-4.9651142318)) < (4.9651142318 : ℝ) := by
    have e1 : Real.exp (-4.9651142318) = Real.exp 0.0348857682 / Real.exp 1 ^ 5 := by
      rw [show (-4.9651142318 : ℝ) = 0.0348857682 - ((5 : ℕ) : ℝ) * 1 by norm_num,
        Real.exp_sub, Real.exp_nat_mul]
    rw [e1]
    obtain ⟨hX1, -⟩ := abs_le.1 (Real.exp_bound (x := (0.0348857682 : ℝ))
      (by rw [abs_of_pos (by norm_num)]; norm_num) (n := 7) (by norm_num))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.0348857682)] at hX1
    norm_num [Finset.sum_range_succ, Nat.factorial] at hX1
    have h5 : Real.exp 1 ^ 5 ≤ ((363916618873 : ℝ) / 133877442384 + 1 / 10 ^ 20) ^ 5 :=
      pow_le_pow_left₀ hEpos.le (by linarith) 5
    have h5' := mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 1 - 4.9651142318 / 5)
    have key : 1 - 4.9651142318 / 5 < Real.exp 0.0348857682 / Real.exp 1 ^ 5 := by
      rw [lt_div_iff₀ (by positivity)]
      norm_num at h5' ⊢
      linarith
    linarith
  obtain ⟨hpos, hneg⟩ := W2m_BlackbodyRadiation_root_sign 5 (by norm_num) x hx hroot
  constructor
  · by_contra H
    push_neg at H
    rcases H.lt_or_eq with h | h
    · have := hneg _ h
      linarith
    · rw [← h] at hlo
      linarith
  · by_contra H
    push_neg at H
    rcases H.lt_or_eq with h | h
    · have := hpos _ (by norm_num) h
      linarith
    · rw [h] at hhi
      linarith

theorem solution
    (n : ℝ) (hn : 1 < n) :
    ∃! x : ℝ, 0 < x ∧ x = n * (1 - Real.exp (-x)) := by
  apply W2m_BlackbodyRadiation_existsUnique_pos_root_maximisation_equation <;> assumption
