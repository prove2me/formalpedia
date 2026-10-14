-- Prove2me | solution 1 for DistCov.Converse.twoPointLaw_not_isProduct
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T02:51:24.936991+00:00
-- url     : https://prove2.me/submissions/9bf48afe-ac97-4dad-93ee-38de790408b4

import Definitions.Def_DistCov_Converse_Setting
import Theorems.Thm_DistCov_Converse_Ddiff_dirac_neg
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
open DistCov.Indep DistCov.Converse
namespace DistCovNonproduct
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
lemma dist_integrable (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) (x : X) :
    Integrable (fun z => dist x z) μ := by
  obtain ⟨o,ho⟩ := h
  apply ((integrable_const (dist x o)).add ho).mono' (by fun_prop)
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Pi.add_apply] using dist_triangle x o z

lemma dist_prod_integrable (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν) :
    Integrable (fun p : X × X => dist p.1 p.2) (μ.prod ν) := by
  obtain ⟨o, ho⟩ := hμ
  have hi := (ho.comp_fst ν).add ((dist_integrable ν hν o).comp_snd μ)
  apply hi.mono' (by fun_prop)
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Pi.add_apply,
    Function.comp_apply, dist_comm p.1 o] using dist_triangle p.1 o p.2

lemma energy_symm (μ ν : Measure X) [SFinite μ] [SFinite ν] : energy ν μ = energy μ ν := by
  unfold energy
  have h := integral_prod_swap (μ := μ) (ν := ν) (fun p : X × X => dist p.1 p.2)
  simpa only [Prod.fst_swap, Prod.snd_swap, dist_comm] using h

lemma dirac_moment (x : X) : FiniteFirstMoment (Measure.dirac x) :=
  ⟨x, integrable_dirac (by simp)⟩

lemma weighted_prod_integrable (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν) (a b : ℝ) :
    Integrable (fun p : X × X => dist p.1 p.2)
      ((ENNReal.ofReal a • μ).prod (ENNReal.ofReal b • ν)) := by
  rw [Measure.prod_smul_left, Measure.prod_smul_right]
  exact ((dist_prod_integrable μ ν hμ hν).smul_measure ENNReal.ofReal_ne_top).smul_measure
    ENNReal.ofReal_ne_top

lemma mix_probability (μ : Measure X) [IsProbabilityMeasure μ] (x : X)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : IsProbabilityMeasure (mixDirac r μ x) := by
  constructor
  simp only [mixDirac, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hr.1 (sub_nonneg.mpr hr.2)]
  simp

lemma mix_moment (μ : Measure X) [IsProbabilityMeasure μ] (hμ : FiniteFirstMoment μ)
    (x : X) (r : ℝ) : FiniteFirstMoment (mixDirac r μ x) := by
  refine ⟨x, ?_⟩
  exact integrable_add_measure.mpr
    ⟨(dist_integrable μ hμ x).smul_measure ENNReal.ofReal_ne_top,
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top⟩


lemma energy_right_mix (κ μ : Measure X) [IsProbabilityMeasure κ] [IsProbabilityMeasure μ]
    (hκ : FiniteFirstMoment κ) (hμ : FiniteFirstMoment μ) (x : X)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    energy κ (mixDirac r μ x) = r * energy κ μ + (1-r) * energy κ (Measure.dirac x) := by
  have hA : Integrable (fun p : X × X => dist p.1 p.2)
      (κ.prod (ENNReal.ofReal r • μ)) := by
    rw [Measure.prod_smul_right]
    exact (dist_prod_integrable κ μ hκ hμ).smul_measure ENNReal.ofReal_ne_top
  have hB : Integrable (fun p : X × X => dist p.1 p.2)
      (κ.prod (ENNReal.ofReal (1-r) • Measure.dirac x)) := by
    rw [Measure.prod_smul_right]
    exact (dist_prod_integrable κ _ hκ (dirac_moment x)).smul_measure ENNReal.ofReal_ne_top
  unfold energy mixDirac
  rw [Measure.prod_add, integral_add_measure hA hB]
  simp only [Measure.prod_smul_right, integral_smul_measure,
    ENNReal.toReal_ofReal hr.1, ENNReal.toReal_ofReal (sub_nonneg.mpr hr.2), smul_eq_mul]

lemma mixtures_ne (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν)
    (hne : μ ≠ ν) (hD : 0 ≤ Ddiff μ ν) (x y : X) (hx : x ≠ y)
    (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) : mixDirac r μ x ≠ mixDirac r ν y := by
  intro heq
  by_cases hr1 : r = 1
  · subst r
    apply hne
    simpa [mixDirac] using heq
  have hri : r ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hr.1, hr.2⟩
  have htest (κ : Measure X) [IsProbabilityMeasure κ] (hκ : FiniteFirstMoment κ) :
      r * (energy κ μ - energy κ ν) +
        (1-r) * (energy κ (Measure.dirac x) - energy κ (Measure.dirac y)) = 0 := by
    have he := congrArg (energy κ) heq
    rw [energy_right_mix κ μ hκ hμ x r hri, energy_right_mix κ ν hκ hν y r hri] at he
    linarith
  let B := energy μ (Measure.dirac x) - energy μ (Measure.dirac y) -
    energy ν (Measure.dirac x) + energy ν (Measure.dirac y)
  have hfirst : r * Ddiff μ ν + (1-r) * B = 0 := by
    have hμtest := htest μ hμ
    have hνtest := htest ν hν
    rw [energy_symm μ ν] at hνtest
    unfold Ddiff B
    linarith
  have hsecond : r * B + (1-r) * Ddiff (Measure.dirac x) (Measure.dirac y) = 0 := by
    have hxtest := htest (Measure.dirac x) (dirac_moment x)
    have hytest := htest (Measure.dirac y) (dirac_moment y)
    rw [energy_symm μ (Measure.dirac x), energy_symm ν (Measure.dirac x)] at hxtest
    rw [energy_symm μ (Measure.dirac y), energy_symm ν (Measure.dirac y),
      energy_symm (Measure.dirac x) (Measure.dirac y)] at hytest
    unfold Ddiff B
    linarith
  have hidentity : r ^ 2 * Ddiff μ ν = (1-r) ^ 2 * Ddiff (Measure.dirac x) (Measure.dirac y) := by
    have ha := congrArg (fun t : ℝ => r * t) hfirst
    have hb := congrArg (fun t : ℝ => (1-r) * t) hsecond
    nlinarith [ha, hb]
  have hs : 0 < 1-r := sub_pos.mpr (lt_of_le_of_ne hr.2 hr1)
  have hn := DistCov.Converse.Ddiff_dirac_neg x y hx
  have hneg : (1-r) ^ 2 * Ddiff (Measure.dirac x) (Measure.dirac y) < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_pos hs) hn
  have hnonneg : 0 ≤ r ^ 2 * Ddiff μ ν := mul_nonneg (sq_nonneg r) hD
  linarith

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
local notation "c" => (2 : ℝ≥0∞)⁻¹

def avg (μ ν : Measure X) : Measure X := c • (μ + ν)

instance avg_prob (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (avg μ ν) := by
  constructor
  norm_num [avg, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

lemma marg_fst (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y z : Y) : (twoPointLaw μ ν y z).map Prod.fst = avg μ ν := by
  simp [twoPointLaw, avg, Measure.map_smul, Measure.map_add, measurable_fst,
    Measure.map_fst_prod, smul_add]

lemma marg_snd (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y z : Y) : (twoPointLaw μ ν y z).map Prod.snd = avg (Measure.dirac y) (Measure.dirac z) := by
  simp [twoPointLaw, avg, Measure.map_smul, Measure.map_add, measurable_snd,
    Measure.map_snd_prod, smul_add]


lemma product_forces_eq (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y z : Y) (hy : y ≠ z) (h : IsProduct (twoPointLaw μ ν y z)) : μ = ν := by
  unfold IsProduct at h
  rw [marg_fst, marg_snd] at h
  apply Measure.ext
  intro A hA
  have he := congrArg (fun η : Measure (X × Y) => η (A ×ˢ {y})) h
  have hmass : c * μ A = (c * (μ A + ν A)) * c := by
    simpa [twoPointLaw, avg, Measure.smul_apply, Measure.add_apply, Measure.prod_prod,
      Measure.dirac_apply', hy, Ne.symm hy, hA, mul_add] using he
  have hre := congrArg ENNReal.toReal hmass
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top ν A)] at hre
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp
  linarith

end DistCovNonproduct

open DistCovNonproduct

theorem solution
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : FiniteFirstMoment μ₁) (hμ₂ : FiniteFirstMoment μ₂)
    (hne : μ₁ ≠ μ₂) (hD : 0 ≤ Ddiff μ₁ μ₂) (x₁ x₂ : X) (hx : x₁ ≠ x₂)
    (γ : ℝ) (hγ : γ ∈ Ioc (0 : ℝ) 1) (y₁ y₂ : Y) (hy : y₁ ≠ y₂) :
    ¬ IsProduct (twoPointLaw (mixDirac γ μ₁ x₁) (mixDirac γ μ₂ x₂) y₁ y₂) := by
  have hgi : γ ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hγ.1, hγ.2⟩
  letI := mix_probability μ₁ x₁ γ hgi
  letI := mix_probability μ₂ x₂ γ hgi
  intro hp
  exact mixtures_ne μ₁ μ₂ hμ₁ hμ₂ hne hD x₁ x₂ hx γ hγ
    (product_forces_eq _ _ y₁ y₂ hy hp)

#print axioms solution
