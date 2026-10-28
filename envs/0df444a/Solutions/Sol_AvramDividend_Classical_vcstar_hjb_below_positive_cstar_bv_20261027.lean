-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_hjb_below_positive_cstar_bv_20261027
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:18:54.293804+00:00
-- url     : https://prove2.me/submissions/d2ac96c9-9e79-4086-ae41-227603b093d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_laplace_family
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hcpos : 0 < cstar W) :
    ∀ y ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  intro y hy
  set c : ℝ := (cstar W).toReal with hc
  have hy0 : 0 < y := hy.1
  have hyc : y < c := hy.2
  have hc0 : 0 < c := lt_trans hy0 hyc
  have hne : cstar W ≠ ⊤ := by
    intro h; rw [hc, h] at hc0; simp at hc0
  have hS : (cstarSet W).Nonempty := by
    by_contra hS
    have : cstar W = 0 ∨ cstar W = ⊤ := by
      unfold cstar; rw [if_neg hS]; split_ifs <;> simp
    rcases this with h | h
    · rw [h] at hcpos; exact lt_irrefl _ hcpos
    · exact hne h
  have hcdef : cstar W = ⨅ a ∈ cstarSet W, ENNReal.ofReal a := by
    unfold cstar; rw [if_pos hS]
  have hcof : cstar W = ENNReal.ofReal c := (ENNReal.ofReal_toReal hne).symm
  have hC1 := scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hbv
  have hdcont : ContinuousOn (deriv W) (Ioi 0) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  -- c belongs to cstarSet
  have hcmin : ∀ z : ℝ, 0 < z → deriv W c ≤ deriv W z := by
    intro z hz
    by_contra hlt
    push Not at hlt
    have hca : ContinuousAt (deriv W) c := hdcont.continuousAt (isOpen_Ioi.mem_nhds hc0)
    have hev : ∀ᶠ a in 𝓝 c, deriv W z < deriv W a :=
      hca.eventually (lt_mem_nhds hlt)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hlt2 : cstar W < ENNReal.ofReal (c + δ) := by
      rw [hcof]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    rw [hcdef] at hlt2
    obtain ⟨a, hlt3⟩ := iInf_lt_iff.mp hlt2
    obtain ⟨haS, hlt4⟩ := iInf_lt_iff.mp hlt3
    have hca' : c ≤ a := by
      have : cstar W ≤ ENNReal.ofReal a := by
        rw [hcdef]; exact iInf₂_le a haS
      rw [hcof] at this
      exact (ENNReal.ofReal_le_ofReal_iff haS.1.le).mp this
    have hac : a < c + δ := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hlt4
    have hda := hball (show dist a c < δ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    have := haS.2 z hz
    linarith
  -- k = W'(c) > 0
  obtain ⟨hWpos, φ, hφ, hmono⟩ := scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  have hWd : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ W z := fun z hz =>
    (hC1.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hk : 0 < deriv W c := by
    have hd : HasDerivAt (fun x : ℝ => Real.exp (-φ * x) * W x)
        ((Real.exp (-φ * c) * (-φ * 1)) * W c + Real.exp (-φ * c) * deriv W c) c := by
      have h1 : HasDerivAt (fun x : ℝ => -φ * x) (-φ * 1) c :=
        (hasDerivAt_id c).const_mul (-φ)
      exact h1.exp.mul (hWd c hc0).hasDerivAt
    have h0 := hmono.derivWithin_nonneg (x := c)
    rw [derivWithin_of_isOpen isOpen_Ioi hc0, hd.deriv] at h0
    have hWc := hWpos c hc0
    have hex := Real.exp_pos (-φ * c)
    have : 0 ≤ Real.exp (-φ * c) * (deriv W c - φ * W c) := by nlinarith
    have h2 : 0 ≤ deriv W c - φ * W c := nonneg_of_mul_nonneg_right (by linarith) hex
    nlinarith
  set k := deriv W c with hkdef
  -- vcstar = W / k on Iic c
  have hv : ∀ x : ℝ, x ≤ c → vcstar W x = W x / k := by
    intro x hx
    unfold vcstar barrierValue
    rw [← hc]
    by_cases hx0 : x < 0
    · rw [if_pos hx0, hW.1 x hx0, zero_div]
    · rw [if_neg hx0, if_pos hx]
      unfold divE scaleDeriv
      rw [if_neg hc0.ne', if_neg (EReal.coe_ne_top _), EReal.toReal_coe]
  have hvev : vcstar W =ᶠ[𝓝 y] fun x => W x / k := by
    filter_upwards [Iio_mem_nhds hyc] with x hx using hv x (le_of_lt hx)
  have hdv : deriv (vcstar W) y = deriv W y / k := by
    rw [hvev.deriv_eq, deriv_div_const]
  have hgi : ∀ z ∈ Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand (vcstar W) y z =
      SpectrallyNegativeLevy.generatorIntegrand W y z / k := by
    intro z hz
    have hz' : z < 0 := hz
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [hdv, hv (y + z) (by linarith), hv y hyc.le]
    field_simp
  have hintW : X.GeneratorIntegrable W y :=
    scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one X q W hW hbv y hy0 hC1
  have hintv : X.GeneratorIntegrable (vcstar W) y := by
    have : IntegrableOn (fun z => SpectrallyNegativeLevy.generatorIntegrand W y z / k) (Iio 0) X.ν :=
      Integrable.div_const hintW k
    refine this.congr_fun (fun z hz => ?_) measurableSet_Iio
    rw [hgi z hz]
  have hharm := scaleFunction_generator_interval_harmonic_of_laplace_family X hX q hq W hW
    c hc0
    (generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero X hX hbv hbv.1 q W hW hC1)
    (bv_weighted_generator_residual_family_from_scale_20261026 X hX hbv q hq W hW)
    (fun z hz => scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one X q W hW hbv z
      hz.1 hC1) y hy
  have hgen : X.generator (vcstar W) y = X.generator W y / k := by
    unfold SpectrallyNegativeLevy.generator
    rw [hbv.1, hdv, setIntegral_congr_fun measurableSet_Iio hgi, integral_div]
    ring
  refine ⟨hintv, ?_⟩
  have e1 : X.generator (vcstar W) y - q * vcstar W y = 0 := by
    rw [hgen, hv y hyc.le]
    have := hharm.2
    field_simp
    linarith
  have e2 : 1 - deriv (vcstar W) y ≤ 0 := by
    rw [hdv, sub_nonpos, le_div_iff₀ hk, one_mul]
    exact hcmin y hy0
  rw [e1]
  exact max_eq_left e2
