-- Prove2me | solution 1 for DistCov.Converse.dcov_twoPointLaw
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T00:08:30.173225+00:00
-- url     : https://prove2.me/submissions/0abed44e-7a5f-4711-b7a0-4859757df0b5

import Definitions.Def_DistCov_Converse_Setting
import Theorems.Thm_DistCov_Indep_dcov_integrable
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open DistCov.Indep DistCov.Converse
namespace DistCovTwoPoint
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
lemma dist_integrable (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) (x : X) :
    Integrable (fun z => dist x z) μ := by
  obtain ⟨o,ho⟩ := h
  apply ((integrable_const (dist x o)).add ho).mono' (by fun_prop)
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Pi.add_apply] using dist_triangle x o z

lemma mean_nonneg (μ : Measure X) (x : X) : 0 ≤ meanDist μ x :=
  integral_nonneg (fun _ => dist_nonneg)

lemma mean_meas (μ : Measure X) [SFinite μ] : StronglyMeasurable (meanDist μ) := by
  have hd : StronglyMeasurable (fun p : X × X => dist p.1 p.2) :=
    (continuous_fst.dist continuous_snd).stronglyMeasurable
  exact hd.integral_prod_right'

lemma mean_bound (μ : Measure X) [IsProbabilityMeasure μ] (o : X)
    (ho : Integrable (fun z => dist o z) μ) (x : X) :
    meanDist μ x ≤ dist o x + ∫ z, dist o z ∂μ := by
  have hx := dist_integrable μ ⟨o,ho⟩ x
  unfold meanDist
  calc
    (∫ z, dist x z ∂μ) ≤ ∫ z, (dist o x + dist o z) ∂μ := by
      apply integral_mono hx ((integrable_const _).add ho)
      intro z
      simpa only [dist_comm o x, Pi.add_apply] using dist_triangle x o z
    _ = _ := by rw [integral_add (integrable_const _) ho]; simp

lemma mean_integrable (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) :
    Integrable (meanDist μ) μ := by
  obtain ⟨o,ho⟩ := h
  apply (ho.add (integrable_const (∫ z, dist o z ∂μ))).mono' (mean_meas μ).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mean_nonneg μ x), Pi.add_apply] using mean_bound μ o ho x


local notation "c" => (2 : ℝ≥0∞)⁻¹

def avg (μ ν : Measure X) : Measure X := c • (μ + ν)

instance avg_prob (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (avg μ ν) := by
  constructor
  norm_num [avg, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

lemma avg_moment (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν) : FiniteFirstMoment (avg μ ν) := by
  obtain ⟨o, ho⟩ := hμ
  refine ⟨o, ?_⟩
  exact (integrable_add_measure.mpr ⟨ho, dist_integrable ν hν o⟩).smul_measure (by simp)

lemma dirac_moment (x : X) : FiniteFirstMoment (Measure.dirac x) := by
  exact ⟨x, integrable_dirac (by simp)⟩

lemma marg_fst (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y z : Y) : (twoPointLaw μ ν y z).map Prod.fst = avg μ ν := by
  simp [twoPointLaw, avg, Measure.map_smul, Measure.map_add, measurable_fst,
    Measure.map_fst_prod, smul_add]

lemma marg_snd (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y z : Y) : (twoPointLaw μ ν y z).map Prod.snd = avg (Measure.dirac y) (Measure.dirac z) := by
  simp [twoPointLaw, avg, Measure.map_smul, Measure.map_add, measurable_snd,
    Measure.map_snd_prod, smul_add]

instance law_prob (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y z : Y) : IsProbabilityMeasure (twoPointLaw μ ν y z) := by
  constructor
  norm_num [twoPointLaw, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

lemma four_integrals {A : Type*} [MeasurableSpace A]
    (μ ν : Measure A) [SFinite μ] [SFinite ν] (f : A × A → ℝ)
    (hf : Integrable f ((c • (μ + ν)).prod (c • (μ + ν)))) :
    (∫ p, f p ∂((c • (μ + ν)).prod (c • (μ + ν)))) =
      (∫ p, f p ∂μ.prod μ) / 4 + (∫ p, f p ∂μ.prod ν) / 4 +
      (∫ p, f p ∂ν.prod μ) / 4 + (∫ p, f p ∂ν.prod ν) / 4 := by
  have he : (c • (μ + ν)).prod (c • (μ + ν)) =
      c • (c • ((μ.prod μ + μ.prod ν) + (ν.prod μ + ν.prod ν))) := by
    simp only [Measure.prod_smul_left, Measure.prod_smul_right, Measure.add_prod,
      Measure.prod_add, smul_add]
    ac_rfl
  rw [he] at hf ⊢
  have hi := (integrable_smul_measure (by simp : c ≠ 0) (by simp : c ≠ ⊤)).mp hf
  have hi' := (integrable_smul_measure (by simp : c ≠ 0) (by simp : c ≠ ⊤)).mp hi
  rw [integral_smul_measure, integral_smul_measure,
    integral_add_measure hi'.left_of_add_measure hi'.right_of_add_measure,
    integral_add_measure hi'.left_of_add_measure.left_of_add_measure
      hi'.left_of_add_measure.right_of_add_measure,
    integral_add_measure hi'.right_of_add_measure.left_of_add_measure
      hi'.right_of_add_measure.right_of_add_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

lemma mean_avg_dirac (y z t : Y) :
    meanDist (avg (Measure.dirac y) (Measure.dirac z)) t = (dist t y + dist t z) / 2 := by
  unfold meanDist avg
  rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp))]
  simp
  ring

lemma energy_dirac (x y : X) : energy (Measure.dirac x) (Measure.dirac y) = dist x y := by
  simp [energy, Measure.dirac_prod_dirac]

lemma dist_prod_integrable (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν) :
    Integrable (fun p : X × X => dist p.1 p.2) (μ.prod ν) := by
  obtain ⟨o, ho⟩ := hμ
  have hi := (ho.comp_fst ν).add ((dist_integrable ν hν o).comp_snd μ)
  apply hi.mono' (by fun_prop)
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Pi.add_apply,
    Function.comp_apply, dist_comm p.1 o] using dist_triangle p.1 o p.2

lemma D_avg_dirac (y z : Y) :
    D (avg (Measure.dirac y) (Measure.dirac z)) = dist y z / 2 := by
  have hm := avg_moment (Measure.dirac y) (Measure.dirac z) (dirac_moment y) (dirac_moment z)
  have hi := dist_prod_integrable _ _ hm hm
  unfold D energy
  change (∫ p : Y × Y, dist p.1 p.2 ∂(c • (Measure.dirac y + Measure.dirac z)).prod
    (c • (Measure.dirac y + Measure.dirac z))) = _
  rw [four_integrals _ _ _ hi]
  simp [Measure.dirac_prod_dirac, dist_comm z y]
  ring

lemma centered_atoms (y z : Y) :
    dcent (avg (Measure.dirac y) (Measure.dirac z)) y y = -dist y z / 2 ∧
    dcent (avg (Measure.dirac y) (Measure.dirac z)) y z = dist y z / 2 ∧
    dcent (avg (Measure.dirac y) (Measure.dirac z)) z y = dist y z / 2 ∧
    dcent (avg (Measure.dirac y) (Measure.dirac z)) z z = -dist y z / 2 := by
  simp only [dcent, mean_avg_dirac, D_avg_dirac, dist_self, dist_comm z y]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring
lemma centered_meas (μ : Measure X) [SFinite μ] :
    StronglyMeasurable (fun p : X × X => dcent μ p.1 p.2) := by
  unfold dcent
  exact (((continuous_fst.dist continuous_snd).stronglyMeasurable.sub
    ((mean_meas μ).comp_measurable measurable_fst)).sub
    ((mean_meas μ).comp_measurable measurable_snd)).add stronglyMeasurable_const


lemma mean_cross_integrable (m μ : Measure X) [IsProbabilityMeasure m] [IsProbabilityMeasure μ]
    (hm : FiniteFirstMoment m) (hμ : FiniteFirstMoment μ) : Integrable (meanDist m) μ := by
  obtain ⟨o, ho⟩ := hm
  apply ((dist_integrable μ hμ o).add (integrable_const (∫ z, dist o z ∂m))).mono'
    (mean_meas m).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mean_nonneg m x), Pi.add_apply]
    using mean_bound m o ho x

lemma centered_integral (m μ ν : Measure X)
    [IsProbabilityMeasure m] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : FiniteFirstMoment m) (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν) :
    (∫ p : X × X, dcent m p.1 p.2 ∂μ.prod ν) =
      energy μ ν - (∫ x, meanDist m x ∂μ) - (∫ x, meanDist m x ∂ν) + D m := by
  have hd := dist_prod_integrable μ ν hμ hν
  have ha := (mean_cross_integrable m μ hm hμ).comp_fst ν
  have hb := (mean_cross_integrable m ν hm hν).comp_snd μ
  simp only [dcent]
  rw [integral_add (f := fun p : X × X => dist p.1 p.2 - meanDist m p.1 - meanDist m p.2)
      (g := fun _ => D m) ((hd.sub ha).sub hb) (integrable_const _),
    integral_sub (f := fun p : X × X => dist p.1 p.2 - meanDist m p.1)
      (g := fun p => meanDist m p.2) (hd.sub ha) hb,
    integral_sub (f := fun p : X × X => dist p.1 p.2)
      (g := fun p => meanDist m p.1) hd ha]
  simp [energy, integral_prod, ha, hb]

lemma energy_symm (μ ν : Measure X) [SFinite μ] [SFinite ν] : energy ν μ = energy μ ν := by
  unfold energy
  have h := integral_prod_swap (μ := μ) (ν := ν) (fun p : X × X => dist p.1 p.2)
  simpa only [Prod.fst_swap, Prod.snd_swap, dist_comm] using h

def kernel (m : Measure X) (n : Measure Y) (p : (X × Y) × (X × Y)) : ℝ :=
  dcent m p.1.1 p.2.1 * dcent n p.1.2 p.2.2

lemma kernel_meas (m : Measure X) (n : Measure Y) [SFinite m] [SFinite n] :
    StronglyMeasurable (kernel m n) := by
  exact ((centered_meas m).comp_measurable
    (measurable_fst.fst.prodMk measurable_snd.fst)).mul
    ((centered_meas n).comp_measurable (measurable_fst.snd.prodMk measurable_snd.snd))

lemma slice_integral (μ ν : Measure X) [SFinite μ] [SFinite ν] (y z : Y)
    (f : (X × Y) × (X × Y) → ℝ) (hf : StronglyMeasurable f) :
    (∫ p, f p ∂(μ.prod (Measure.dirac y)).prod (ν.prod (Measure.dirac z))) =
    ∫ p : X × X, f ((p.1, y), (p.2, z)) ∂μ.prod ν := by
  rw [Measure.prod_dirac, Measure.prod_dirac,
    Measure.map_prod_map μ ν measurable_prodMk_right measurable_prodMk_right,
    integral_map (measurable_prodMk_right.prodMap measurable_prodMk_right).aemeasurable
      hf.aestronglyMeasurable]
  rfl

lemma slice_kernel (m : Measure X) (n : Measure Y) [SFinite m] [SFinite n]
    (μ ν : Measure X) [SFinite μ] [SFinite ν] (y z : Y) :
    (∫ p, kernel m n p ∂(μ.prod (Measure.dirac y)).prod (ν.prod (Measure.dirac z))) =
    (∫ p : X × X, dcent m p.1 p.2 ∂μ.prod ν) * dcent n y z := by
  rw [slice_integral μ ν y z _ (kernel_meas m n)]
  exact integral_mul_const (dcent n y z) (fun p : X × X => dcent m p.1 p.2)

end DistCovTwoPoint

open DistCovTwoPoint

theorem solution
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : FiniteFirstMoment μ₁) (hμ₂ : FiniteFirstMoment μ₂)
    (y₁ y₂ : Y) (hy : y₁ ≠ y₂) :
    dcov (twoPointLaw μ₁ μ₂ y₁ y₂) = -(dist y₁ y₂) * Ddiff μ₁ μ₂ / 8 := by
  let m := avg μ₁ μ₂
  let n := avg (Measure.dirac y₁) (Measure.dirac y₂)
  have hm : FiniteFirstMoment m := avg_moment μ₁ μ₂ hμ₁ hμ₂
  have hn : FiniteFirstMoment n := avg_moment _ _ (dirac_moment y₁) (dirac_moment y₂)
  have hθ := DistCov.Indep.dcov_integrable (twoPointLaw μ₁ μ₂ y₁ y₂)
    (by simpa only [marg_fst] using hm) (by simpa only [marg_snd] using hn)
  simp only [marg_fst, marg_snd] at hθ
  change Integrable (kernel m n) ((twoPointLaw μ₁ μ₂ y₁ y₂).prod
    (twoPointLaw μ₁ μ₂ y₁ y₂)) at hθ
  unfold dcov
  simp only [marg_fst, marg_snd]
  change (∫ p, kernel m n p ∂(twoPointLaw μ₁ μ₂ y₁ y₂).prod
    (twoPointLaw μ₁ μ₂ y₁ y₂)) = _
  unfold twoPointLaw
  rw [four_integrals _ _ _ hθ]
  rw [slice_kernel, slice_kernel, slice_kernel, slice_kernel]
  obtain ⟨haa, hab, hba, hbb⟩ := centered_atoms y₁ y₂
  change dcent n y₁ y₁ = _ at haa
  change dcent n y₁ y₂ = _ at hab
  change dcent n y₂ y₁ = _ at hba
  change dcent n y₂ y₂ = _ at hbb
  rw [haa, hab, hba, hbb]
  rw [centered_integral m μ₁ μ₁ hm hμ₁ hμ₁,
    centered_integral m μ₁ μ₂ hm hμ₁ hμ₂,
    centered_integral m μ₂ μ₁ hm hμ₂ hμ₁,
    centered_integral m μ₂ μ₂ hm hμ₂ hμ₂,
    energy_symm μ₁ μ₂]
  unfold Ddiff
  ring

#print axioms solution
