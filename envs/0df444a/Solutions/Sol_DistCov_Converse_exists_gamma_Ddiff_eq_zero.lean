-- Prove2me | solution 1 for DistCov.Converse.exists_gamma_Ddiff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T02:40:40.404198+00:00
-- url     : https://prove2.me/submissions/0668f989-e0af-417e-9936-03e02c2cfec6

import Definitions.Def_DistCov_Converse_Setting
import Theorems.Thm_DistCov_Converse_Ddiff_dirac_neg
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
open DistCov.Indep DistCov.Converse
namespace DistCovInterpolation
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

lemma energy_weighted_sum (μ ν κ η : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] [IsProbabilityMeasure η]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν)
    (hκ : FiniteFirstMoment κ) (hη : FiniteFirstMoment η)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    energy (ENNReal.ofReal a • μ + ENNReal.ofReal b • ν)
      (ENNReal.ofReal c • κ + ENNReal.ofReal d • η) =
    a * c * energy μ κ + a * d * energy μ η +
      b * c * energy ν κ + b * d * energy ν η := by
  have hAC := weighted_prod_integrable μ κ hμ hκ a c
  have hAD := weighted_prod_integrable μ η hμ hη a d
  have hBC := weighted_prod_integrable ν κ hν hκ b c
  have hBD := weighted_prod_integrable ν η hν hη b d
  unfold energy
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add,
    integral_add_measure (hAC.add_measure hAD) (hBC.add_measure hBD),
    integral_add_measure hAC hAD, integral_add_measure hBC hBD]
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, integral_smul_measure,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb,
    ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hd, smul_eq_mul]
  ring

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

lemma energy_mix (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν)
    (x y : X) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    energy (mixDirac r μ x) (mixDirac r ν y) =
      r ^ 2 * energy μ ν + r * (1-r) *
        (energy μ (Measure.dirac y) + energy (Measure.dirac x) ν) +
      (1-r) ^ 2 * energy (Measure.dirac x) (Measure.dirac y) := by
  rw [mixDirac, mixDirac, energy_weighted_sum μ (Measure.dirac x) ν (Measure.dirac y)
    hμ (dirac_moment x) hν (dirac_moment y) r (1-r) r (1-r)
    hr.1 (sub_nonneg.mpr hr.2) hr.1 (sub_nonneg.mpr hr.2)]
  ring

def cross (μ ν : Measure X) (x y : X) : ℝ :=
  energy μ (Measure.dirac x) + energy (Measure.dirac y) ν -
    energy μ (Measure.dirac y) - energy (Measure.dirac x) ν

def polynomial (μ ν : Measure X) (x y : X) (r : ℝ) : ℝ :=
  r ^ 2 * Ddiff μ ν + 2 * r * (1-r) * cross μ ν x y +
    (1-r) ^ 2 * Ddiff (Measure.dirac x) (Measure.dirac y)

lemma Ddiff_mix (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν)
    (x y : X) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    Ddiff (mixDirac r μ x) (mixDirac r ν y) = polynomial μ ν x y r := by
  unfold Ddiff polynomial cross
  rw [energy_mix μ μ hμ hμ x x r hr, energy_mix μ ν hμ hν x y r hr,
    energy_mix ν ν hν hν y y r hr,
    energy_symm μ (Measure.dirac x), energy_symm (Measure.dirac y) ν]
  simp only [Ddiff]
  ring

end DistCovInterpolation


open DistCovInterpolation

theorem solution
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : FiniteFirstMoment μ₁) (hμ₂ : FiniteFirstMoment μ₂)
    (hD : 0 ≤ Ddiff μ₁ μ₂) (x₁ x₂ : X) (hx : x₁ ≠ x₂) :
    ∃ γ ∈ Set.Ioc (0 : ℝ) 1,
      Ddiff (mixDirac γ μ₁ x₁) (mixDirac γ μ₂ x₂) = 0 := by
  let f : ℝ → ℝ := polynomial μ₁ μ₂ x₁ x₂
  have hc : Continuous f := by unfold f polynomial; fun_prop
  have h0 : f 0 < 0 := by
    simpa [f, polynomial] using DistCov.Converse.Ddiff_dirac_neg x₁ x₂ hx
  have h1 : 0 ≤ f 1 := by simpa [f, polynomial] using hD
  have hz : (0 : ℝ) ∈ Icc (f 0) (f 1) := ⟨le_of_lt h0, h1⟩
  obtain ⟨γ, hγ, hroot⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hc.continuousOn hz
  have hgpos : 0 < γ := by
    apply lt_of_le_of_ne hγ.1
    intro heq
    rw [← heq] at hroot
    rw [hroot] at h0
    exact (lt_irrefl 0) h0
  refine ⟨γ, ⟨hgpos, hγ.2⟩, ?_⟩
  rw [Ddiff_mix μ₁ μ₂ hμ₁ hμ₂ x₁ x₂ γ hγ]
  exact hroot

#print axioms solution
