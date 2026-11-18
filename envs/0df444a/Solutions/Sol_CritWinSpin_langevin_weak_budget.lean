-- Prove2me | solution 1 for CritWinSpin.langevin_weak_budget
-- status  : ACCEPTED   (prove)
-- author  : @Maxliu
-- created : 2026-11-17T16:59:47.566248+00:00
-- url     : https://prove2.me/submissions/aa4c9469-ebbf-48d6-b9a4-cf77e7f43867

import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Mathlib

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.DensityAnalysis

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def gibbsDensity {d : ℕ} (V : Point d → ℝ) (x : Point d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-V x))
def partition {d : ℕ} (V : Point d → ℝ) : ℝ≥0∞ := ∫⁻ x, gibbsDensity V x ∂volume
def gibbs {d : ℕ} (V : Point d → ℝ) : Measure (Point d) :=
  (partition V)⁻¹ • volume.withDensity (gibbsDensity V)

lemma lintegral_fin_nat_prod {n : ℕ} {E : Type*}
    [MeasurableSpace E] {μ : Fin n → Measure E}
    [∀ i, SigmaFinite (μ i)] (f : Fin n → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : E × (Fin n → E),
          f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
          ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
        rw [((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_map_equiv]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
        rw [lintegral_prod_mul (g := fun x : Fin n → E => ∏ i, f i.succ (x i))
          (hf 0).aemeasurable
          (Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable, ih _ (fun i => hf _)]
      _ = _ := by rw [Fin.prod_univ_succ]

theorem pi_withDensity_fin {n : ℕ} {E : Type*}
    [MeasurableSpace E] (μ : Fin n → Measure E)
    [∀ i, SigmaFinite (μ i)] (f : Fin n → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [Measure.restrict_pi_pi]
  rw [lintegral_fin_nat_prod _ hf]
  apply Finset.prod_congr rfl
  intro i _
  exact (withDensity_apply _ (hs i)).symm


theorem map_withDensity_of_measurePreserving {E F : Type*}
    [MeasurableSpace E] [MeasurableSpace F] {μ : Measure E} {ν : Measure F}
    (e : E ≃ᵐ F) (he : MeasurePreserving e μ ν) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = ν.withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  have h := he.setLIntegral_comp_preimage hs (hf.comp e.symm.measurable)
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using h


namespace EulerDensity
open ProbabilityTheory MeasureTheory WithLp
open scoped ENNReal NNReal RealInnerProductSpace

def gaussianCoefficient (d : ℕ) : ℝ≥0∞ :=
  ∏ _ : Fin d, ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹)

lemma standard_pi_density (d : ℕ) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 1) =
      (volume : Measure (Fin d → ℝ)).withDensity
        (fun x => gaussianCoefficient d*ENNReal.ofReal (Real.exp (-(∑ k, (x k)^2)/2))) := by
  have hg : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero _ (by norm_num)
  have : IsProbabilityMeasure (volume.withDensity (gaussianPDF 0 1)) := by rw [← hg]; infer_instance
  simp_rw [hg]
  rw [pi_withDensity_fin _ _ (fun _ => measurable_gaussianPDF _ _)]
  congr 1
  ext x
  have he (z : ℝ) : gaussianPDF 0 1 z =
      ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹)*ENNReal.ofReal (Real.exp (-z^2/2)) := by
    simp [gaussianPDF,gaussianPDFReal]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div,Finset.sum_neg_distrib]

theorem standard_density (d : ℕ) :
    stdGaussian (Point d) = gaussianCoefficient d •
      (volume : Measure (Point d)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-‖z‖^2/2))) := by
  rw [← map_pi_eq_stdGaussian,standard_pi_density]
  let e : (Fin d → ℝ) ≃ᵐ Point d := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  change Measure.map e _ = _
  rw [map_withDensity_of_measurePreserving e (PiLp.volume_preserving_toLp (Fin d)) (by fun_prop)]
  have he : (fun y : Point d => gaussianCoefficient d*
      ENNReal.ofReal (Real.exp (-(∑ k, (e.symm y k)^2)/2))) =
      gaussianCoefficient d • (fun z : Point d => ENNReal.ofReal (Real.exp (-‖z‖^2/2))) := by
    funext y
    simp only [Pi.smul_apply,smul_eq_mul]
    congr 3
    change -(∑ k, (y k)^2)/2 = -‖y‖^2/2
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs,sq_abs]
  rw [he,withDensity_smul]
  fun_prop

lemma gaussianCoefficient_positive (d : ℕ) : 0 < gaussianCoefficient d := by
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)

lemma gaussianCoefficient_finite (d : ℕ) : gaussianCoefficient d ≠ ⊤ := by
  exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)

def shear {d : ℕ} (T : Point d → Point d) (hT : Measurable T) :
    Point d × Point d ≃ᵐ Point d × Point d where
  toFun p := (p.1,T p.1+p.2)
  invFun p := (p.1,p.2-T p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk ((hT.comp measurable_fst).add measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub (hT.comp measurable_fst))

lemma shear_measurePreserving {d : ℕ} {T : Point d → Point d} (hT : Measurable T) :
    MeasurePreserving (shear T hT) ((volume : Measure (Point d)).prod volume)
      ((volume : Measure (Point d)).prod volume) := by
  exact (MeasurePreserving.id volume).skew_product ((hT.comp measurable_fst).add measurable_snd)
    (Filter.Eventually.of_forall (fun x => map_add_left_eq_self volume (T x)))

end EulerDensity

namespace EulerDensity
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

lemma map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (e : E ≃ᵐ F) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) :=
  map_withDensity_of_measurePreserving e ⟨e.measurable,rfl⟩ hf

def noiseCoefficient (d : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  gaussianCoefficient d*ENNReal.ofReal |(σ^d)⁻¹|

lemma scaled_standard_density (d : ℕ) {σ : ℝ} (hσ : σ ≠ 0) :
    (stdGaussian (Point d)).map (fun z => σ • z) =
      noiseCoefficient d σ • (volume : Measure (Point d)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-‖z‖^2/(2*σ^2)))) := by
  let e := (Homeomorph.smulOfNeZero (α := Point d) σ hσ).toMeasurableEquiv
  rw [standard_density,Measure.map_smul]
  change gaussianCoefficient d • (Measure.map e _) = _
  rw [map_withDensity_equiv volume e (by fun_prop)]
  have he : (volume : Measure (Point d)).map e =
      ENNReal.ofReal |(σ^d)⁻¹| • volume := by
    convert! Measure.map_addHaar_smul (volume : Measure (Point d)) hσ using 1
    all_goals try with_reducible_and_instances rfl
    simp [Point]
  rw [he,withDensity_smul_measure,smul_smul]
  congr 2
  funext z
  have hz : e.symm z = σ⁻¹ • z := by
    exact congrFun (Homeomorph.smulOfNeZero_symm_apply hσ) z
  rw [hz,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  congr 2
  field_simp

lemma noiseCoefficient_positive (d : ℕ) {σ : ℝ} (hσ : σ ≠ 0) :
    0 < noiseCoefficient d σ := by
  apply ENNReal.mul_pos_iff.mpr
  exact ⟨gaussianCoefficient_positive d,ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hσ)))⟩

lemma noiseCoefficient_finite (d : ℕ) (σ : ℝ) : noiseCoefficient d σ ≠ ⊤ :=
  ENNReal.mul_ne_top (gaussianCoefficient_finite d) ENNReal.ofReal_ne_top

theorem joint_density {d : ℕ} {H : Point d → ℝ} (hH : Measurable H)
    (T : Point d → Point d) (hT : Measurable T) {σ : ℝ} (hσ : σ ≠ 0) :
    ((gibbs H).prod (stdGaussian (Point d))).map (fun p => (p.1,T p.1+σ • p.2)) =
      ((partition H)⁻¹*noiseCoefficient d σ) •
        ((volume : Measure (Point d)).prod volume).withDensity
          (fun p => ENNReal.ofReal (Real.exp (-H p.1-‖p.2-T p.1‖^2/(2*σ^2)))) := by
  have : SFinite (gibbs H) := by unfold gibbs; infer_instance
  have hmap : ((gibbs H).prod (stdGaussian (Point d))).map
      (fun p => (p.1,T p.1+σ • p.2)) =
      (((gibbs H).prod ((stdGaussian (Point d)).map (fun z => σ • z))).map (shear T hT)) := by
    have hj := Measure.map_prod_map (gibbs H) (stdGaussian (Point d)) measurable_id
      (show Measurable (fun z : Point d => σ • z) by fun_prop)
    simp only [Measure.map_id] at hj
    rw [hj,Measure.map_map (shear T hT).measurable (by fun_prop)]
    rfl
  rw [hmap,scaled_standard_density d hσ]
  unfold gibbs
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
    prod_withDensity (by unfold gibbsDensity; fun_prop) (by fun_prop),
    Measure.map_smul,
    map_withDensity_of_measurePreserving (shear T hT) (shear_measurePreserving hT) (by unfold gibbsDensity; fun_prop)]
  congr 2
  funext p
  change ENNReal.ofReal (Real.exp (-H p.1))*
    ENNReal.ofReal (Real.exp (-‖p.2-T p.1‖^2/(2*σ^2))) = _
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

end EulerDensity

lemma partition_toReal {d : ℕ} {H : Point d → ℝ}
    (hi : Integrable (fun x => Real.exp (-H x))) :
    (partition H).toReal = ∫ x, Real.exp (-H x) := by
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-H x)).le)
    hi.aestronglyMeasurable).symm

lemma integral_gibbs {d : ℕ} {H : Point d → ℝ} (hc : Continuous H)
    (hi : Integrable (fun x => Real.exp (-H x))) (f : Point d → ℝ) :
    (∫ x, f x ∂gibbs H) = (∫ x, Real.exp (-H x) * f x) / ∫ x, Real.exp (-H x) := by
  rw [gibbs,integral_smul_measure,ENNReal.toReal_inv,partition_toReal hi]
  have hden : Measurable (gibbsDensity H) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hden
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f]
  simp only [gibbsDensity,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]
  ring

lemma integrable_gibbs_of_weighted {d : ℕ} {H f : Point d → ℝ} (hc : Continuous H)
    (hi : Integrable (fun x => Real.exp (-H x)))
    (hf : Integrable (fun x => Real.exp (-H x) * f x)) : Integrable f (gibbs H) := by
  have hp : partition H ≠ ⊤ := (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-H x)).le)).2 hi
  have hpos : 0 < partition H := by
    have hmeasure : Measurable (gibbsDensity H) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
    rw [partition,lintegral_pos_iff_support hmeasure]
    have hh : Function.support (gibbsDensity H) = Set.univ := by
      ext x
      simp [Function.mem_support,gibbsDensity,not_le_of_gt (Real.exp_pos (-H x))]
    rw [hh]
    exact isOpen_univ.measure_pos volume Set.univ_nonempty
  have hw : Integrable f (volume.withDensity (gibbsDensity H)) := by
    have hden : Measurable (gibbsDensity H) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
    rw [integrable_withDensity_iff_integrable_smul' hden
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [gibbsDensity,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul] using hf
  exact hw.smul_measure (by simpa using hpos.ne')


theorem partition_eq_ofReal {d : ℕ} {H : Point d → ℝ}
    (hi : Integrable (fun x => Real.exp (-H x))) :
    partition H = ENNReal.ofReal (∫ x, Real.exp (-H x)) :=
  (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-H x)).le)).symm

theorem gibbs_probability {d : ℕ} {H : Point d → ℝ}
    (hi : Integrable (fun x => Real.exp (-H x))) : IsProbabilityMeasure (gibbs H) := by
  have hp : partition H ≠ 0 := by
    rw [partition_eq_ofReal hi]
    exact (ENNReal.ofReal_pos.mpr (integral_exp_pos hi)).ne'
  have ht : partition H ≠ ⊤ := by rw [partition_eq_ofReal hi]; exact ENNReal.ofReal_ne_top
  constructor
  rw [gibbs, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hp ht

end CritWinSpin.Implementation.DensityAnalysis

end

end

section

set_option autoImplicit false
open MeasureTheory

namespace CritWinSpin.Implementation.MetropolisFlux

variable {E : Type*} [MeasurableSpace E]

def accepted (F : E × E → ℝ) (p : E × E) : ℝ := min (F p) (F p.swap)
def rejected (F : E × E → ℝ) (p : E × E) : ℝ := F p - accepted F p

theorem accepted_nonneg {F : E × E → ℝ} (hF : ∀ p, 0 ≤ F p) (p : E × E) :
    0 ≤ accepted F p := le_min (hF p) (hF p.swap)

theorem rejected_nonneg {F : E × E → ℝ} (p : E × E) : 0 ≤ rejected F p :=
  sub_nonneg.mpr (min_le_left _ _)

theorem accepted_le {F : E × E → ℝ} (p : E × E) : accepted F p ≤ F p :=
  min_le_left _ _

theorem rejected_le {F : E × E → ℝ} (hF : ∀ p, 0 ≤ F p) (p : E × E) :
    rejected F p ≤ F p := sub_le_self _ (accepted_nonneg hF p)

theorem accepted_swap (F : E × E → ℝ) (p : E × E) :
    accepted F p.swap = accepted F p := by simp [accepted, min_comm]

theorem accepted_balance (μ : Measure E) [SFinite μ]
    (F : E × E → ℝ) (f : E → ℝ) :
    ∫ p, accepted F p * (f p.2 - f p.1) ∂μ.prod μ = 0 := by
  have hs := integral_prod_swap (μ := μ) (ν := μ)
    (fun p : E × E => accepted F p * (f p.2 - f p.1))
  have he : (fun p : E × E => accepted F p.swap * (f p.1 - f p.2)) =
      fun p => -(accepted F p * (f p.2 - f p.1)) := by
    funext p
    rw [accepted_swap]
    ring
  change (∫ p, accepted F p.swap * (f p.1 - f p.2) ∂μ.prod μ) = _ at hs
  rw [he, integral_neg] at hs
  linarith

theorem accepted_integrable (μ : Measure E) [SFinite μ]
    {F : E × E → ℝ} (hF : ∀ p, 0 ≤ F p) (hmF : Measurable F)
    (hiF : Integrable F (μ.prod μ)) : Integrable (accepted F) (μ.prod μ) := by
  refine hiF.mono' (hmF.min (hmF.comp measurable_swap)).aestronglyMeasurable ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (accepted_nonneg hF p)]
  exact accepted_le p

theorem rejected_integrable (μ : Measure E) [SFinite μ]
    {F : E × E → ℝ} (hF : ∀ p, 0 ≤ F p) (hmF : Measurable F)
    (hiF : Integrable F (μ.prod μ)) : Integrable (rejected F) (μ.prod μ) :=
  hiF.sub (accepted_integrable μ hF hmF hiF)

theorem bounded_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {g h : Ω → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hig : Integrable g μ) (hmh : Measurable h) {B : ℝ} (hB : 0 ≤ B)
    (hh : ∀ x, |h x| ≤ B) : Integrable (fun x => g x * h x) μ := by
  refine (hig.mul_const B).mono' (hig.aestronglyMeasurable.mul hmh.aestronglyMeasurable) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg x)]
  exact mul_le_mul_of_nonneg_left (hh x) (hg x)

theorem flux_defect (μ : Measure E) [SFinite μ]
    {F : E × E → ℝ} (hF : ∀ p, 0 ≤ F p) (hmF : Measurable F)
    (hiF : Integrable F (μ.prod μ))
    {f : E → ℝ} (hmf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) :
    (∫ p, F p * (f p.2 - f p.1) ∂μ.prod μ) =
      ∫ p, rejected F p * (f p.2 - f p.1) ∂μ.prod μ := by
  have hm := (hmf.comp measurable_snd).sub (hmf.comp measurable_fst)
  have hb : ∀ p : E × E, |f p.2 - f p.1| ≤ 2 * B := fun p =>
    (abs_sub _ _).trans (by linarith [hf p.2, hf p.1])
  have hia := bounded_product_integrable (μ.prod μ) (accepted_nonneg hF)
    (accepted_integrable μ hF hmF hiF) hm (by positivity : 0 ≤ 2 * B) hb
  have hir := bounded_product_integrable (μ.prod μ) rejected_nonneg
    (rejected_integrable μ hF hmF hiF) hm (by positivity : 0 ≤ 2 * B) hb
  change Integrable (fun p => accepted F p * (f p.2 - f p.1)) (μ.prod μ) at hia
  change Integrable (fun p => rejected F p * (f p.2 - f p.1)) (μ.prod μ) at hir
  have he : (fun p : E × E => F p * (f p.2 - f p.1)) =
      fun p => accepted F p * (f p.2 - f p.1) + rejected F p * (f p.2 - f p.1) := by
    funext p
    simp only [rejected]
    ring
  rw [he, integral_add hia hir, accepted_balance, zero_add]

theorem lipschitz_defect [PseudoMetricSpace E]
    (μ : Measure E) [SFinite μ]
    {F : E × E → ℝ} (hF : ∀ p, 0 ≤ F p) (hmF : Measurable F)
    (hiF : Integrable F (μ.prod μ))
    {f : E → ℝ} (hmf : Measurable f) {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hf : ∀ x, |f x| ≤ B) (hLip : ∀ x y, |f y - f x| ≤ L * dist x y)
    (hiD : Integrable (fun p => rejected F p * dist p.1 p.2) (μ.prod μ)) :
    |∫ p, F p * (f p.2 - f p.1) ∂μ.prod μ| ≤
      L * (∫ p, rejected F p * dist p.1 p.2 ∂μ.prod μ) := by
  rw [flux_defect μ hF hmF hiF hmf hB hf]
  have hm := (hmf.comp measurable_snd).sub (hmf.comp measurable_fst)
  have hb : ∀ p : E × E, |f p.2 - f p.1| ≤ 2 * B := fun p =>
    (abs_sub _ _).trans (by linarith [hf p.2, hf p.1])
  have hir := bounded_product_integrable (μ.prod μ) rejected_nonneg
    (rejected_integrable μ hF hmF hiF) hm (by positivity : 0 ≤ 2 * B) hb
  have hn := norm_integral_le_integral_norm (μ := μ.prod μ)
    (f := fun p => rejected F p * (f p.2 - f p.1))
  rw [Real.norm_eq_abs] at hn
  calc
    _ ≤ ∫ p, |rejected F p * (f p.2 - f p.1)| ∂μ.prod μ := hn
    _ ≤ ∫ p, L * (rejected F p * dist p.1 p.2) ∂μ.prod μ := by
      apply integral_mono hir.abs (hiD.const_mul L)
      intro p
      change |rejected F p * (f p.2 - f p.1)| ≤ L * (rejected F p * dist p.1 p.2)
      rw [abs_mul, abs_of_nonneg (rejected_nonneg p)]
      have hh := mul_le_mul_of_nonneg_left (hLip p.1 p.2) (rejected_nonneg (F := F) p)
      nlinarith only [hh]
    _ = _ := integral_const_mul _ _

theorem rejected_exponential (u v : ℝ) :
    Real.exp u - min (Real.exp u) (Real.exp v) ≤ Real.exp u * |v - u| := by
  by_cases h : u ≤ v
  · rw [min_eq_left (Real.exp_le_exp.mpr h), sub_self]
    positivity
  · have hvu : v ≤ u := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right (Real.exp_le_exp.mpr hvu), abs_of_nonpos (sub_nonpos.mpr hvu)]
    have he : 1 + (v - u) ≤ Real.exp (v - u) := by linarith [Real.add_one_le_exp (v - u)]
    have hp := mul_le_mul_of_nonneg_left he (Real.exp_pos u).le
    rw [← Real.exp_add] at hp
    have heq : u + (v - u) = v := by ring
    rw [heq] at hp
    nlinarith

end CritWinSpin.Implementation.MetropolisFlux

end

section

set_option autoImplicit false
open scoped RealInnerProductSpace
noncomputable section

namespace CritWinSpin.Implementation.LangevinAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def drift (g : E → E) (γ : ℝ) (x : E) : E := x - γ • g x

theorem drift_sq_contract {g : E → E} {a γ : ℝ}
    (ha : 0 ≤ a) (hγ : 0 ≤ γ) (hstep : 16 * γ ≤ a)
    (hmono : ∀ x y, a * ‖x - y‖ ^ 2 ≤ (inner ℝ (x - y) (g x - g y)))
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖) (x y : E) :
    ‖drift g γ x - drift g γ y‖ ^ 2 ≤ (1 - a * γ) * ‖x - y‖ ^ 2 := by
  have he : drift g γ x - drift g γ y = (x - y) - γ • (g x - g y) := by
    simp only [drift, smul_sub]
    abel
  have hl : ‖g x - g y‖ ^ 2 ≤ 16 * ‖x - y‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 4 * ‖x - y‖)).2 (hLip x y)
    nlinarith only [h]
  rw [he, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hm := hmono x y
  have hh := mul_le_mul_of_nonneg_left hl (sq_nonneg γ)
  have h₁ := mul_le_mul_of_nonneg_left hm hγ
  have h₂ := mul_le_mul_of_nonneg_right hstep (mul_nonneg hγ (sq_nonneg ‖x - y‖))
  nlinarith only [hh, h₁, h₂]

theorem drift_contract {g : E → E} {a γ : ℝ}
    (ha : 0 ≤ a) (hγ : 0 ≤ γ) (hsmall : a * γ ≤ 1) (hstep : 16 * γ ≤ a)
    (hmono : ∀ x y, a * ‖x - y‖ ^ 2 ≤ (inner ℝ (x - y) (g x - g y)))
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖) (x y : E) :
    ‖drift g γ x - drift g γ y‖ ≤ (1 - a * γ / 2) * ‖x - y‖ := by
  have hc := drift_sq_contract ha hγ hstep hmono hLip x y
  have hq : 0 ≤ 1 - a * γ / 2 := by linarith
  have ht : (1 - a * γ) * ‖x - y‖ ^ 2 ≤ ((1 - a * γ / 2) * ‖x - y‖) ^ 2 := by
    nlinarith [sq_nonneg (a * γ * ‖x - y‖)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg _))).1 (hc.trans ht)

def proposalLog (U : E → ℝ) (g : E → E) (γ : ℝ) (x y : E) : ℝ :=
  -U x - ‖y - x + γ • g x‖ ^ 2 / (4 * γ)

def trapezoid (U : E → ℝ) (g : E → E) (x y : E) : ℝ :=
  U y - U x - (1 / 2) * (inner ℝ (y - x) (g x + g y))

theorem log_ratio (U : E → ℝ) (g : E → E) {γ : ℝ} (hγ : γ ≠ 0) (x y : E) :
    proposalLog U g γ x y - proposalLog U g γ y x =
      trapezoid U g x y + γ / 4 * (‖g y‖ ^ 2 - ‖g x‖ ^ 2) := by
  have he : x - y = -(y - x) := by abel
  simp only [proposalLog, trapezoid, he, norm_add_sq_real, norm_neg, norm_smul,
    Real.norm_eq_abs, real_inner_smul_right, inner_neg_left, inner_add_right, mul_pow, sq_abs]
  field_simp
  ring

theorem trapezoid_bound {U : E → ℝ} {g : E → E}
    (hTaylor : ∀ x y, |U y - U x - (inner ℝ (y - x) (g x))| ≤ ‖y - x‖ ^ 2) (x y : E) :
    |trapezoid U g x y| ≤ ‖y - x‖ ^ 2 := by
  have hf := hTaylor x y
  have hr := hTaylor y x
  rw [show x - y = -(y - x) by abel, norm_neg, inner_neg_left] at hr
  rw [abs_le] at hf hr ⊢
  simp only [trapezoid, inner_add_right]
  constructor <;> linarith

theorem norm_sq_difference (u v : E) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ ‖u - v‖ * (‖u‖ + ‖v‖) := by
  rw [show ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u v)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem log_ratio_bound {U : E → ℝ} {g : E → E} {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hTaylor : ∀ x y, |U y - U x - (inner ℝ (y - x) (g x))| ≤ ‖y - x‖ ^ 2)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖) (x y : E) :
    |proposalLog U g γ x y - proposalLog U g γ y x| ≤
      5 * ‖y - x‖ ^ 2 + 2 * γ * ‖y - x‖ * ‖g x‖ := by
  have hD := norm_sq_difference (g y) (g x)
  have hd := hLip y x
  have hgy : ‖g y‖ ≤ ‖g x‖ + 4 * ‖y - x‖ := by
    have hn := norm_add_le (g x) (g y - g x)
    rw [add_sub_cancel] at hn
    linarith
  have hg : |‖g y‖ ^ 2 - ‖g x‖ ^ 2| ≤
      8 * ‖y - x‖ * ‖g x‖ + 16 * ‖y - x‖ ^ 2 := by
    calc
      _ ≤ 4 * ‖y - x‖ * (‖g y‖ + ‖g x‖) :=
        hD.trans (mul_le_mul_of_nonneg_right hd (by positivity))
      _ ≤ 4 * ‖y - x‖ * ((‖g x‖ + 4 * ‖y - x‖) + ‖g x‖) := by gcongr
      _ = _ := by ring
  rw [log_ratio U g hγ.ne']
  calc
    _ ≤ |trapezoid U g x y| + |γ / 4 * (‖g y‖ ^ 2 - ‖g x‖ ^ 2)| := abs_add_le _ _
    _ ≤ ‖y - x‖ ^ 2 + (γ / 4) * (8 * ‖y - x‖ * ‖g x‖ + 16 * ‖y - x‖ ^ 2) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ γ / 4)]
      exact add_le_add (trapezoid_bound hTaylor x y) (mul_le_mul_of_nonneg_left hg (by positivity))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hγ1 (sq_nonneg ‖y - x‖)]

def proposal (g : E → E) (s : ℝ) (x z : E) : E :=
  x - s ^ 2 • g x + (Real.sqrt 2 * s) • z

theorem proposal_distance {g : E → E} {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (x z : E) :
    ‖proposal g s x z - x‖ ≤ s * (‖g x‖ + 2 * ‖z‖) := by
  have he : proposal g s x z - x = -(s ^ 2 • g x) + (Real.sqrt 2 * s) • z := by
    dsimp [proposal]
    abel
  rw [he]
  calc
    _ ≤ ‖-(s ^ 2 • g x)‖ + ‖(Real.sqrt 2 * s) • z‖ := norm_add_le _ _
    _ = s ^ 2 * ‖g x‖ + (Real.sqrt 2 * s) * ‖z‖ := by
      rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg s), abs_of_nonneg (by positivity)]
    _ ≤ s * ‖g x‖ + (2 * s) * ‖z‖ := by
      have hs2 : s ^ 2 ≤ s := by nlinarith
      have hr2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
      gcongr
    _ = _ := by ring

theorem cubic_sum_bound (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    (r + 2 * t) ^ 3 ≤ 32 * (2 + r ^ 6 + t ^ 6) := by
  have hs := add_pow_le hr (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ht) 3
  norm_num at hs
  have hr6 : r ^ 3 ≤ 1 + r ^ 6 := by nlinarith [sq_nonneg (r ^ 3 - 1 / 2)]
  have ht6 : t ^ 3 ≤ 1 + t ^ 6 := by nlinarith [sq_nonneg (t ^ 3 - 1 / 2)]
  have hr3 := pow_nonneg hr 3
  nlinarith

theorem weighted_log_ratio_bound {U : E → ℝ} {g : E → E} {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hTaylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖) (x z : E) :
    ‖proposal g s x z - x‖ *
        |proposalLog U g (s ^ 2) x (proposal g s x z) - proposalLog U g (s ^ 2) (proposal g s x z) x| ≤
      224 * s ^ 3 * (2 + ‖g x‖ ^ 6 + ‖z‖ ^ 6) := by
  let D := ‖proposal g s x z - x‖
  let W := ‖g x‖ + 2 * ‖z‖
  have hD : D ≤ s * W := proposal_distance hs.le hs1 x z
  have hD0 : 0 ≤ D := norm_nonneg _
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hl := log_ratio_bound (sq_pos_of_pos hs) hs2 hTaylor hLip x (proposal g s x z)
  change |proposalLog U g (s ^ 2) x (proposal g s x z) - proposalLog U g (s ^ 2) (proposal g s x z) x| ≤
    5 * D ^ 2 + 2 * s ^ 2 * D * ‖g x‖ at hl
  have hD2 : D ^ 2 ≤ s ^ 2 * W ^ 2 := by nlinarith [sq_le_sq₀ hD0 (mul_nonneg hs.le hW) |>.2 hD]
  have hG : ‖g x‖ ≤ W := by dsimp [W]; linarith [norm_nonneg z]
  have hcross : D * ‖g x‖ ≤ s * W ^ 2 := by
    calc
      _ ≤ (s * W) * W := mul_le_mul hD hG (norm_nonneg _) (mul_nonneg hs.le hW)
      _ = _ := by ring
  have hs3 : s ^ 3 ≤ s ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hs1 (sq_nonneg s)]
  have hlog : |proposalLog U g (s ^ 2) x (proposal g s x z) -
      proposalLog U g (s ^ 2) (proposal g s x z) x| ≤ 7 * s ^ 2 * W ^ 2 := by
    have hc := mul_le_mul_of_nonneg_left hcross (by positivity : 0 ≤ 2 * s ^ 2)
    have ht := mul_le_mul_of_nonneg_right hs3 (sq_nonneg W)
    nlinarith only [hl, hD2, hc, ht]
  calc
    _ ≤ (s * W) * (7 * s ^ 2 * W ^ 2) :=
      mul_le_mul hD hlog (abs_nonneg _) (mul_nonneg hs.le hW)
    _ = 7 * s ^ 3 * W ^ 3 := by ring
    _ ≤ 7 * s ^ 3 * (32 * (2 + ‖g x‖ ^ 6 + ‖z‖ ^ 6)) :=
      mul_le_mul_of_nonneg_left (cubic_sum_bound ‖g x‖ ‖z‖ (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

theorem weighted_rejection_bound {U : E → ℝ} {g : E → E} {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hTaylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖) (x z : E) :
    (Real.exp (proposalLog U g (s ^ 2) x (proposal g s x z)) -
        min (Real.exp (proposalLog U g (s ^ 2) x (proposal g s x z)))
          (Real.exp (proposalLog U g (s ^ 2) (proposal g s x z) x))) * ‖proposal g s x z - x‖ ≤
      Real.exp (proposalLog U g (s ^ 2) x (proposal g s x z)) *
        (224 * s ^ 3 * (2 + ‖g x‖ ^ 6 + ‖z‖ ^ 6)) := by
  have he := MetropolisFlux.rejected_exponential
    (proposalLog U g (s ^ 2) x (proposal g s x z))
    (proposalLog U g (s ^ 2) (proposal g s x z) x)
  rw [abs_sub_comm] at he
  calc
    _ ≤ (Real.exp (proposalLog U g (s ^ 2) x (proposal g s x z)) *
        |proposalLog U g (s ^ 2) x (proposal g s x z) - proposalLog U g (s ^ 2) (proposal g s x z) x|) *
          ‖proposal g s x z - x‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ = Real.exp (proposalLog U g (s ^ 2) x (proposal g s x z)) *
        (‖proposal g s x z - x‖ * |proposalLog U g (s ^ 2) x (proposal g s x z) -
          proposalLog U g (s ^ 2) (proposal g s x z) x|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_log_ratio_bound hs hs1 hTaylor hLip x z) (Real.exp_pos _).le

end CritWinSpin.Implementation.LangevinAlgebra

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.DensityIntegrals

variable {Ω : Type*} [MeasurableSpace Ω]

def weighted (μ : Measure Ω) (F : Ω → ℝ) : Measure Ω := μ.withDensity fun x => ENNReal.ofReal (F x)

theorem integral_weighted (μ : Measure Ω) {F : Ω → ℝ}
    (hF : ∀ x, 0 ≤ F x) (hmF : Measurable F) (g : Ω → ℝ) :
    (∫ x, g x ∂weighted μ F) = ∫ x, F x * g x ∂μ := by
  rw [weighted, integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (F x)) (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hF _), smul_eq_mul]

theorem integrable_weighted_iff (μ : Measure Ω) {F : Ω → ℝ}
    (hF : ∀ x, 0 ≤ F x) (hmF : Measurable F) (g : Ω → ℝ) :
    Integrable g (weighted μ F) ↔ Integrable (fun x => F x * g x) μ := by
  rw [weighted, integrable_withDensity_iff_integrable_smul'
    (f := fun x => ENNReal.ofReal (F x)) (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hF _), smul_eq_mul]

theorem density_integrable (μ : Measure Ω) {F : Ω → ℝ}
    (hF : ∀ x, 0 ≤ F x) (hmF : Measurable F)
    [IsProbabilityMeasure (weighted μ F)] : Integrable F μ := by
  have hi : Integrable (fun _ : Ω => (1 : ℝ)) (weighted μ F) := integrable_const _
  rw [integrable_weighted_iff μ hF hmF] at hi
  simpa only [mul_one] using hi

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

def correction (F : E × E → ℝ) (p : E × E) : ℝ :=
  MetropolisFlux.rejected F p / F p * dist p.1 p.2

theorem correction_nonneg {F : E × E → ℝ} (hF : ∀ p, 0 ≤ F p) (p : E × E) :
    0 ≤ correction F p := mul_nonneg (div_nonneg (MetropolisFlux.rejected_nonneg p) (hF p)) dist_nonneg

theorem density_mul_correction {F : E × E → ℝ} (hF : ∀ p, 0 < F p) (p : E × E) :
    F p * correction F p = MetropolisFlux.rejected F p * dist p.1 p.2 := by
  dsimp [correction]
  field_simp [(hF p).ne']

theorem probability_defect (μ : Measure E) [SFinite μ]
    {F : E × E → ℝ} (hF : ∀ p, 0 < F p) (hmF : Measurable F)
    [IsProbabilityMeasure (weighted (μ.prod μ) F)]
    (hiC : Integrable (correction F) (weighted (μ.prod μ) F))
    {f : E → ℝ} (hmf : Measurable f) {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hf : ∀ x, |f x| ≤ B) (hLip : ∀ x y, |f y - f x| ≤ L * dist x y) :
    |∫ p, f p.2 - f p.1 ∂weighted (μ.prod μ) F| ≤
      L * (∫ p, correction F p ∂weighted (μ.prod μ) F) := by
  have hiF := density_integrable (μ.prod μ) (fun p => (hF p).le) hmF
  have hiD : Integrable (fun p => MetropolisFlux.rejected F p * dist p.1 p.2) (μ.prod μ) := by
    rw [integrable_weighted_iff (μ.prod μ) (fun p => (hF p).le) hmF] at hiC
    simpa only [density_mul_correction hF] using hiC
  rw [integral_weighted (μ.prod μ) (fun p => (hF p).le) hmF,
    integral_weighted (μ.prod μ) (fun p => (hF p).le) hmF]
  simp only [density_mul_correction hF]
  exact MetropolisFlux.lipschitz_defect μ (fun p => (hF p).le) hmF hiF hmf hB hL hf hLip hiD

end CritWinSpin.Implementation.DensityIntegrals

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.LangevinJointDensity

open DensityAnalysis LangevinAlgebra

def coefficient {d : ℕ} (U : Point d → ℝ) (s : ℝ) : ℝ≥0∞ :=
  (partition U)⁻¹ * EulerDensity.noiseCoefficient d (Real.sqrt 2 * s)

def flux {d : ℕ} (U : Point d → ℝ) (g : Point d → Point d) (s : ℝ)
    (p : Point d × Point d) : ℝ :=
  (coefficient U s).toReal * Real.exp (proposalLog U g (s ^ 2) p.1 p.2)

def proposalMap {d : ℕ} (g : Point d → Point d) (s : ℝ) (p : Point d × Point d) : Point d × Point d :=
  (p.1, proposal g s p.1 p.2)

theorem coefficient_nonzero_finite {d : ℕ} {U : Point d → ℝ} {s : ℝ}
    (hi : Integrable (fun x => Real.exp (-U x))) (hs : s ≠ 0) :
    coefficient U s ≠ 0 ∧ coefficient U s ≠ ⊤ := by
  have hp : partition U ≠ 0 := by
    rw [partition_eq_ofReal hi]
    exact (ENNReal.ofReal_pos.mpr (integral_exp_pos hi)).ne'
  have ht : partition U ≠ ⊤ := by rw [partition_eq_ofReal hi]; exact ENNReal.ofReal_ne_top
  have hσ : Real.sqrt 2 * s ≠ 0 := mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)) hs
  exact ⟨mul_ne_zero (ENNReal.inv_ne_zero.mpr ht) (EulerDensity.noiseCoefficient_positive d hσ).ne',
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp) (EulerDensity.noiseCoefficient_finite _ _)⟩

theorem flux_pos {d : ℕ} {U : Point d → ℝ} {g : Point d → Point d} {s : ℝ}
    (hi : Integrable (fun x => Real.exp (-U x))) (hs : s ≠ 0) (p : Point d × Point d) :
    0 < flux U g s p := by
  have hc := coefficient_nonzero_finite hi hs
  exact mul_pos (ENNReal.toReal_pos hc.1 hc.2) (Real.exp_pos _)

theorem flux_measurable {d : ℕ} {U : Point d → ℝ} {g : Point d → Point d} (s : ℝ)
    (hU : Continuous U) (hg : Continuous g) : Measurable (flux U g s) := by
  unfold flux proposalLog
  fun_prop

theorem proposalMap_measurable {d : ℕ} {g : Point d → Point d} (s : ℝ) (hg : Continuous g) :
    Measurable (proposalMap g s) := by
  unfold proposalMap proposal
  fun_prop

theorem joint_density {d : ℕ} {U : Point d → ℝ} {g : Point d → Point d} {s : ℝ}
    (hU : Continuous U) (hg : Continuous g)
    (hi : Integrable (fun x => Real.exp (-U x))) (hs : s ≠ 0) :
    ((DensityAnalysis.gibbs U).prod (stdGaussian (Point d))).map (proposalMap g s) =
      DensityIntegrals.weighted ((volume : Measure (Point d)).prod volume) (flux U g s) := by
  have hσ : Real.sqrt 2 * s ≠ 0 := mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)) hs
  have hT : Measurable (drift g (s ^ 2)) := by unfold drift; fun_prop
  have hj := EulerDensity.joint_density hU.measurable (drift g (s ^ 2)) hT hσ
  have hexp : (fun p : Point d × Point d => ENNReal.ofReal
      (Real.exp (-U p.1 - ‖p.2 - drift g (s ^ 2) p.1‖ ^ 2 / (2 * (Real.sqrt 2 * s) ^ 2)))) =
      fun p => ENNReal.ofReal (Real.exp (proposalLog U g (s ^ 2) p.1 p.2)) := by
    funext p
    have hv : p.2 - drift g (s ^ 2) p.1 = p.2 - p.1 + s ^ 2 • g p.1 := by unfold drift; abel
    rw [hv, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    congr 3
    ring
  change ((DensityAnalysis.gibbs U).prod (stdGaussian (Point d))).map
    (fun p => (p.1, drift g (s ^ 2) p.1 + (Real.sqrt 2 * s) • p.2)) = _
  rw [hj, hexp]
  change coefficient U s • ((volume : Measure (Point d)).prod volume).withDensity
      (fun p => ENNReal.ofReal (Real.exp (proposalLog U g (s ^ 2) p.1 p.2))) = _
  rw [← withDensity_smul _ (by unfold proposalLog; fun_prop)]
  unfold DensityIntegrals.weighted
  congr 1
  funext p
  simp only [Pi.smul_apply, smul_eq_mul, flux,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (coefficient_nonzero_finite hi hs).2]

theorem correction_proposal_bound {d : ℕ} {U : Point d → ℝ} {g : Point d → Point d} {s : ℝ}
    (hi : Integrable (fun x => Real.exp (-U x))) (hs : 0 < s) (hs1 : s ≤ 1)
    (hTaylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖) (x z : Point d) :
    DensityIntegrals.correction (flux U g s) (proposalMap g s (x,z)) ≤
      224 * s ^ 3 * (2 + ‖g x‖ ^ 6 + ‖z‖ ^ 6) := by
  let y := proposal g s x z
  let c := (coefficient U s).toReal
  let A := Real.exp (proposalLog U g (s ^ 2) x y)
  let B := Real.exp (proposalLog U g (s ^ 2) y x)
  have hc : 0 < c := by
    have hh := coefficient_nonzero_finite hi hs.ne'
    exact ENNReal.toReal_pos hh.1 hh.2
  have hA : 0 < A := Real.exp_pos _
  have he := weighted_rejection_bound hs hs1 hTaylor hLip x z
  change (A - min A B) * ‖y - x‖ ≤ A * (224 * s ^ 3 * (2 + ‖g x‖ ^ 6 + ‖z‖ ^ 6)) at he
  unfold DensityIntegrals.correction MetropolisFlux.rejected MetropolisFlux.accepted
  change (c * A - min (c * A) (c * B)) / (c * A) * dist x y ≤ _
  rw [← mul_min_of_nonneg _ _ hc.le, ← mul_sub, mul_div_mul_left _ _ hc.ne', dist_eq_norm, norm_sub_rev]
  apply (le_of_mul_le_mul_right ?_ hA)
  calc
    _ = (A - min A B) * ‖y - x‖ := by field_simp [hA.ne']
    _ ≤ A * (224 * s ^ 3 * (2 + ‖g x‖ ^ 6 + ‖z‖ ^ 6)) := he
    _ = _ := by ring

end CritWinSpin.Implementation.LangevinJointDensity

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace CritWinSpin.Implementation.GaussianMoments

def sixthConstant : ℝ := ∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 1

theorem sixth_integrable : Integrable (fun x : ℝ => |x| ^ 6) (gaussianReal 0 1) := by
  simpa only [Real.norm_eq_abs, id_eq] using
    (memLp_id_gaussianReal (μ := 0) (v := 1) 6).integrable_norm_pow' (p := 6)

theorem sixth_nonneg : 0 ≤ sixthConstant := integral_nonneg fun _ => by positivity

theorem norm_sixth_pointwise (N : ℕ) (z : EuclideanSpace ℝ (Fin N)) :
    ‖z‖ ^ 6 ≤ (N : ℝ) ^ 2 * ∑ i, |z i| ^ 6 := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := (Finset.univ : Finset (Fin N))) (f := fun i => (z i) ^ 2)
    (p := 3) (by norm_num) (fun i _ => sq_nonneg (z i))
  norm_num [Real.rpow_natCast, ← pow_mul] at h
  have hn : ‖z‖ ^ 6 = (∑ i, z i ^ 2) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, EuclideanSpace.real_norm_sq_eq]
  rw [hn]
  have habs : ∀ i : Fin N, |z i| ^ 6 = z i ^ 6 := by
    intro i
    simp only [show (6 : ℕ) = 2 * 3 by decide, pow_mul, sq_abs]
  simp_rw [habs]
  exact h

theorem coordinate_map (N : ℕ) (i : Fin N) :
    (stdGaussian (EuclideanSpace ℝ (Fin N))).map (fun z => z i) = gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map (fun z => z i) = _
  exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).map_eq

theorem coordinate_sixth_integrable (N : ℕ) (i : Fin N) :
    Integrable (fun z : EuclideanSpace ℝ (Fin N) => |z i| ^ 6) (stdGaussian _) := by
  have hi := sixth_integrable
  rw [← coordinate_map N i] at hi
  exact hi.comp_measurable (by fun_prop)

theorem coordinate_sixth_integral (N : ℕ) (i : Fin N) :
    (∫ z : EuclideanSpace ℝ (Fin N), |z i| ^ 6 ∂stdGaussian _) = sixthConstant := by
  rw [sixthConstant, ← coordinate_map N i,
    integral_map (by fun_prop) (by fun_prop)]

theorem norm_sixth_integrable (N : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin N) => ‖z‖ ^ 6) (stdGaussian _) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin N))) 6 (by norm_num)).integrable_norm_pow' (p := 6)

theorem norm_sixth_integral (N : ℕ) :
    (∫ z : EuclideanSpace ℝ (Fin N), ‖z‖ ^ 6 ∂stdGaussian _) ≤ sixthConstant * (N : ℝ) ^ 3 := by
  have hu : Integrable (fun z : EuclideanSpace ℝ (Fin N) => (N : ℝ) ^ 2 * ∑ i, |z i| ^ 6)
      (stdGaussian _) :=
    (integrable_finset_sum _ fun i _ => coordinate_sixth_integrable N i).const_mul _
  calc
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin N), (N : ℝ) ^ 2 * (∑ i, |z i| ^ 6) ∂stdGaussian _ :=
      integral_mono (norm_sixth_integrable N) hu (norm_sixth_pointwise N)
    _ = (N : ℝ) ^ 2 * ∑ i : Fin N, (∫ z : EuclideanSpace ℝ (Fin N), |z i| ^ 6 ∂stdGaussian _) := by
      rw [integral_const_mul, integral_finset_sum _ fun i _ => coordinate_sixth_integrable N i]
    _ = sixthConstant * (N : ℝ) ^ 3 := by simp only [coordinate_sixth_integral, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end CritWinSpin.Implementation.GaussianMoments

end

end

section

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CritWinSpin.Implementation.ContractiveOperator

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

def BoundedLip (f : E → ℝ) (B L : ℝ) : Prop :=
  Measurable f ∧ (∀ x, |f x| ≤ B) ∧ (∀ x y, |f x - f y| ≤ L * dist x y)

theorem bounded_integrable {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ} {B L : ℝ} (hf : BoundedLip f B L) : Integrable f μ := by
  refine (integrable_const B).mono' hf.1.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hf.2.1 x

variable (P : (E → ℝ) → E → ℝ) (q : ℝ)

theorem boundedLip_iterate (hq : 0 ≤ q)
    (hP : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L → BoundedLip (P f) B (q * L))
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) (n : ℕ) :
    BoundedLip (P^[n] f) B (q ^ n * L) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    convert hP _ B (q ^ n * L) (mul_nonneg (pow_nonneg hq n) hL) ih using 1 <;>
      simp only [pow_succ] <;> ring

theorem geometric_sum_bound (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, q ^ j) ≤ 1 / (1 - q) := by
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  apply (le_div_iff₀ hd).2
  have hs : (∑ j ∈ Finset.range n, q ^ j) * (1 - q) = 1 - q ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring
  rw [hs]
  exact sub_le_self _ (pow_nonneg hq n)

theorem iterated_defect (μ : Measure E) [IsProbabilityMeasure μ] (b : ℝ)
    (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hP : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L → BoundedLip (P f) B (q * L))
    (hstep : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      |(∫ x, P f x ∂μ) - ∫ x, f x ∂μ| ≤ L * b)
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) (n : ℕ) :
    |(∫ x, (P^[n] f) x ∂μ) - ∫ x, f x ∂μ| ≤
      L * b * (∑ j ∈ Finset.range n, q ^ j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hf' := boundedLip_iterate P q hq hP hL hf n
    have hs := hstep (P^[n] f) B (q ^ n * L) (by positivity) hf'
    have ht := abs_sub_le (∫ x, P (P^[n] f) x ∂μ)
      (∫ x, (P^[n] f) x ∂μ) (∫ x, f x ∂μ)
    rw [Finset.sum_range_succ]
    nlinarith

theorem from_point (μ : Measure E) [IsProbabilityMeasure μ] (b : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hb : 0 ≤ b)
    (hP : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L → BoundedLip (P f) B (q * L))
    (hstep : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      |(∫ x, P f x ∂μ) - ∫ x, f x ∂μ| ≤ L * b)
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L)
    (x₀ : E) (hi : Integrable (fun x => dist x₀ x) μ) (n : ℕ) :
    |(P^[n] f) x₀ - ∫ x, f x ∂μ| ≤
      q ^ n * L * (∫ x, dist x₀ x ∂μ) + L * b / (1 - q) := by
  have hf' := boundedLip_iterate P q hq hP hL hf n
  have hint : Integrable (P^[n] f) μ := bounded_integrable hf'
  have hp : |(P^[n] f) x₀ - ∫ x, (P^[n] f) x ∂μ| ≤
      q ^ n * L * (∫ x, dist x₀ x ∂μ) := by
    have he : (P^[n] f) x₀ - ∫ x, (P^[n] f) x ∂μ =
        ∫ x, (P^[n] f) x₀ - (P^[n] f) x ∂μ := by
      rw [integral_sub (integrable_const _) hint, integral_const, probReal_univ, one_smul]
    rw [he]
    have hn := norm_integral_le_integral_norm (μ := μ)
      (f := fun x => (P^[n] f) x₀ - (P^[n] f) x)
    rw [Real.norm_eq_abs] at hn
    calc
      _ ≤ ∫ x, |(P^[n] f) x₀ - (P^[n] f) x| ∂μ := hn
      _ ≤ ∫ x, q ^ n * L * dist x₀ x ∂μ :=
        integral_mono ((integrable_const _).sub hint).abs (hi.const_mul _) (fun x => hf'.2.2 x₀ x)
      _ = _ := integral_const_mul _ _
  have hd := iterated_defect P q μ b hq hb hP hstep hL hf n
  have hg := mul_le_mul_of_nonneg_left (geometric_sum_bound q hq hq1 n) (mul_nonneg hL hb)
  have ht := abs_sub_le ((P^[n] f) x₀) (∫ x, (P^[n] f) x ∂μ) (∫ x, f x ∂μ)
  have he : L * b * (1 / (1 - q)) = L * b / (1 - q) := by ring
  rw [he] at hg
  linarith

theorem bounded_iterate {Q : (E → ℝ) → E → ℝ}
    (hQ : ∀ (f : E → ℝ) (B : ℝ), Measurable f → (∀ x, |f x| ≤ B) →
      Measurable (Q f) ∧ ∀ x, |Q f x| ≤ B)
    {f : E → ℝ} {B : ℝ} (hm : Measurable f) (hb : ∀ x, |f x| ≤ B) (n : ℕ) :
    Measurable (Q^[n] f) ∧ ∀ x, |(Q^[n] f) x| ≤ B := by
  induction n with
  | zero => exact ⟨hm, hb⟩
  | succ n ih => rw [Function.iterate_succ_apply']; exact hQ _ B ih.1 ih.2

theorem perturbed_iterates {Q : (E → ℝ) → E → ℝ} (e : ℝ)
    (hq : 0 ≤ q) (he : 0 ≤ e)
    (hP : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L → BoundedLip (P f) B (q * L))
    (hQ : ∀ (f : E → ℝ) (B : ℝ), Measurable f → (∀ x, |f x| ≤ B) →
      Measurable (Q f) ∧ ∀ x, |Q f x| ≤ B)
    (hQC : ∀ (f g : E → ℝ) (B D : ℝ), Measurable f → Measurable g →
      (∀ x, |f x| ≤ B) → (∀ x, |g x| ≤ B) → (∀ x, |f x - g x| ≤ D) →
      ∀ x, |Q f x - Q g x| ≤ D)
    (hstep : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      ∀ x, |Q f x - P f x| ≤ L * e)
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) (n : ℕ) (x : E) :
    |(Q^[n] f) x - (P^[n] f) x| ≤ L * e * (∑ j ∈ Finset.range n, q ^ j) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hp := boundedLip_iterate P q hq hP hL hf n
    have hqf := bounded_iterate hQ hf.1 hf.2.1 n
    have hc := hQC (Q^[n] f) (P^[n] f) B
      (L * e * (∑ j ∈ Finset.range n, q ^ j)) hqf.1 hp.1 hqf.2 hp.2.1 ih x
    have hs := hstep (P^[n] f) B (q ^ n * L) (by positivity) hp x
    have ht := abs_sub_le (Q (Q^[n] f) x) (Q (P^[n] f) x) (P (P^[n] f) x)
    rw [Finset.sum_range_succ]
    nlinarith

theorem perturbed_from_point {Q : (E → ℝ) → E → ℝ}
    (μ : Measure E) [IsProbabilityMeasure μ] (b e : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hP : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L → BoundedLip (P f) B (q * L))
    (hQ : ∀ (f : E → ℝ) (B : ℝ), Measurable f → (∀ x, |f x| ≤ B) →
      Measurable (Q f) ∧ ∀ x, |Q f x| ≤ B)
    (hQC : ∀ (f g : E → ℝ) (B D : ℝ), Measurable f → Measurable g →
      (∀ x, |f x| ≤ B) → (∀ x, |g x| ≤ B) → (∀ x, |f x - g x| ≤ D) →
      ∀ x, |Q f x - Q g x| ≤ D)
    (hstep : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      |(∫ x, P f x ∂μ) - ∫ x, f x ∂μ| ≤ L * b)
    (happrox : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      ∀ x, |Q f x - P f x| ≤ L * e)
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L)
    (x₀ : E) (hi : Integrable (fun x => dist x₀ x) μ) (n : ℕ) :
    |(Q^[n] f) x₀ - ∫ x, f x ∂μ| ≤
      q ^ n * L * (∫ x, dist x₀ x ∂μ) + L * (b + e) / (1 - q) := by
  have hp := from_point P q μ b hq hq1 hb hP hstep hL hf x₀ hi n
  have hQ' := perturbed_iterates P q e hq he hP hQ hQC happrox hL hf n x₀
  have hg := mul_le_mul_of_nonneg_left (geometric_sum_bound q hq hq1 n) (mul_nonneg hL he)
  have ht := abs_sub_le ((Q^[n] f) x₀) ((P^[n] f) x₀) (∫ x, f x ∂μ)
  have hEq : L * (b + e) / (1 - q) = L * b / (1 - q) + L * e * (1 / (1 - q)) := by ring
  rw [hEq]
  linarith

end CritWinSpin.Implementation.ContractiveOperator

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace CritWinSpin.Implementation.NoiseOperator

open ContractiveOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def operator (ν : Measure E) (T : E → E) (σ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z, f (T x + σ • z) ∂ν

theorem bounded_integrable_noise (ν : Measure E) [IsProbabilityMeasure ν]
    {T : E → E} {σ : ℝ} {f : E → ℝ} {B : ℝ}
    (hmf : Measurable f) (hf : ∀ x, |f x| ≤ B) (x : E) :
    Integrable (fun z => f (T x + σ • z)) ν := by
  refine (integrable_const B).mono' (hmf.comp (measurable_const.add (measurable_id.const_smul σ))).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hf (T x + σ • z)

theorem measurable_operator (ν : Measure E) [SFinite ν]
    {T : E → E} (hT : Measurable T) (σ : ℝ) {f : E → ℝ} (hf : Measurable f) :
    Measurable (operator ν T σ f) := by
  exact (hf.comp ((hT.comp measurable_fst).add (measurable_snd.const_smul σ))).stronglyMeasurable.integral_prod_right'.measurable

theorem operator_bound (ν : Measure E) [IsProbabilityMeasure ν]
    (T : E → E) (σ : ℝ) {f : E → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) (x : E) :
    |operator ν T σ f x| ≤ B := by
  have hn := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun z => f (T x + σ • z))
    (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hf (T x + σ • z))
  simpa only [operator, Real.norm_eq_abs, probReal_univ, mul_one] using hn

theorem operator_lipschitz (ν : Measure E) [IsProbabilityMeasure ν]
    {T : E → E} {q : ℝ≥0} (hT : LipschitzWith q T) (σ : ℝ)
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) (x y : E) :
    |operator ν T σ f x - operator ν T σ f y| ≤ ((q : ℝ) * L) * dist x y := by
  rw [operator, operator, ← integral_sub
    (bounded_integrable_noise ν hf.1 hf.2.1 x) (bounded_integrable_noise ν hf.1 hf.2.1 y)]
  have hp : ∀ z, |f (T x + σ • z) - f (T y + σ • z)| ≤ ((q : ℝ) * L) * dist x y := by
    intro z
    have hh := hf.2.2 (T x + σ • z) (T y + σ • z)
    rw [dist_add_right] at hh
    have hd := mul_le_mul_of_nonneg_left (hT.dist_le_mul x y) hL
    nlinarith only [hh, hd]
  have hn := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun z => f (T x + σ • z) - f (T y + σ • z))
    (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hp z)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hn

theorem preserves_boundedLip (ν : Measure E) [IsProbabilityMeasure ν]
    {T : E → E} {q : ℝ≥0} (hT : LipschitzWith q T) (σ : ℝ)
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) :
    BoundedLip (operator ν T σ f) B ((q : ℝ) * L) :=
  ⟨measurable_operator ν hT.continuous.measurable σ hf.1,
    operator_bound ν T σ hf.2.1, operator_lipschitz ν hT σ hL hf⟩

theorem supnorm_nonexpansive (ν : Measure E) [IsProbabilityMeasure ν]
    (T : E → E) (σ : ℝ) {f g : E → ℝ} {B D : ℝ}
    (hmf : Measurable f) (hmg : Measurable g)
    (hf : ∀ x, |f x| ≤ B) (hg : ∀ x, |g x| ≤ B)
    (hd : ∀ x, |f x - g x| ≤ D) (x : E) :
    |operator ν T σ f x - operator ν T σ g x| ≤ D := by
  rw [operator, operator, ← integral_sub
    (bounded_integrable_noise ν hmf hf x) (bounded_integrable_noise ν hmg hg x)]
  have hn := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun z => f (T x + σ • z) - g (T x + σ • z))
    (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hd (T x + σ • z))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hn

theorem drift_perturbation (ν : Measure E) [IsProbabilityMeasure ν]
    (T T' : E → E) (σ : ℝ) {f : E → ℝ} {B L e : ℝ}
    (hL : 0 ≤ L) (hf : BoundedLip f B L) (hT : ∀ x, dist (T x) (T' x) ≤ e) (x : E) :
    |operator ν T σ f x - operator ν T' σ f x| ≤ L * e := by
  rw [operator, operator, ← integral_sub
    (bounded_integrable_noise ν hf.1 hf.2.1 x) (bounded_integrable_noise ν hf.1 hf.2.1 x)]
  have hp : ∀ z, |f (T x + σ • z) - f (T' x + σ • z)| ≤ L * e := by
    intro z
    have hh := hf.2.2 (T x + σ • z) (T' x + σ • z)
    rw [dist_add_right] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hT x) hL)
  have hn := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun z => f (T x + σ • z) - f (T' x + σ • z))
    (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hp z)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hn

theorem noise_perturbation (ν ν' : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (T : E → E) (σ : ℝ) (ε : ℝ)
    (hnoise : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      |(∫ z, f z ∂ν) - ∫ z, f z ∂ν'| ≤ L * ε)
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) (x : E) :
    |operator ν T σ f x - operator ν' T σ f x| ≤ |σ| * L * ε := by
  have hLip : ∀ u v : E,
      |f (T x + σ • u) - f (T x + σ • v)| ≤ (|σ| * L) * dist u v := by
    intro u v
    have hh := hf.2.2 (T x + σ • u) (T x + σ • v)
    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs] at hh
    nlinarith only [hh]
  exact hnoise (fun z => f (T x + σ • z)) B (|σ| * L) (by positivity)
    ⟨hf.1.comp (measurable_const.add (measurable_id.const_smul σ)),
      fun z => hf.2.1 _, hLip⟩

theorem operator_map_smul (ν : Measure E) (T : E → E) (s k : ℝ)
    {f : E → ℝ} (hf : Measurable f) (x : E) :
    operator (ν.map (fun z => k • z)) T s f x = operator ν T (s * k) f x := by
  unfold operator
  have hm : Measurable (fun z : E => f (T x + s • z)) := by
    exact hf.comp (measurable_const.add (measurable_id.const_smul s))
  rw [integral_map (f := fun z : E => f (T x + s • z)) (by fun_prop) hm.aestronglyMeasurable]
  simp only [smul_smul]

end CritWinSpin.Implementation.NoiseOperator

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.LangevinDefect

open DensityAnalysis LangevinAlgebra LangevinJointDensity

theorem correction_measurable {d : ℕ} {U : Point d → ℝ} {g : Point d → Point d} (s : ℝ)
    (hU : Continuous U) (hg : Continuous g) :
    Measurable (DensityIntegrals.correction (flux U g s)) := by
  have hF := flux_measurable s hU hg
  unfold DensityIntegrals.correction MetropolisFlux.rejected MetropolisFlux.accepted
  fun_prop

theorem correction_integrable_and_bound {d : ℕ} {U : Point d → ℝ} {g : Point d → Point d} {s : ℝ}
    (hU : Continuous U) (hg : Continuous g)
    (hiU : Integrable (fun x => Real.exp (-U x))) (hs : 0 < s) (hs1 : s ≤ 1)
    (hTaylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖)
    (hiG : Integrable (fun x => ‖g x‖ ^ 6) (DensityAnalysis.gibbs U)) :
    let J := DensityIntegrals.weighted ((volume : Measure (Point d)).prod volume) (flux U g s)
    Integrable (DensityIntegrals.correction (flux U g s)) J ∧
      (∫ p, DensityIntegrals.correction (flux U g s) p ∂J) ≤
        224 * s ^ 3 * (2 + (∫ x, ‖g x‖ ^ 6 ∂DensityAnalysis.gibbs U) +
          GaussianMoments.sixthConstant * (d : ℝ) ^ 3) := by
  letI : IsProbabilityMeasure (DensityAnalysis.gibbs U) := gibbs_probability hiU
  let μ := (DensityAnalysis.gibbs U).prod (stdGaussian (Point d))
  let J := DensityIntegrals.weighted ((volume : Measure (Point d)).prod volume) (flux U g s)
  let R := DensityIntegrals.correction (flux U g s)
  let H : Point d × Point d → ℝ := fun p => 224 * s ^ 3 * (2 + ‖g p.1‖ ^ 6 + ‖p.2‖ ^ 6)
  have hiZ := GaussianMoments.norm_sixth_integrable d
  have hiG' : Integrable (fun p : Point d × Point d => ‖g p.1‖ ^ 6) μ := hiG.comp_fst _
  have hiZ' : Integrable (fun p : Point d × Point d => ‖p.2‖ ^ 6) μ := hiZ.comp_snd _
  have hiH : Integrable H μ := (((integrable_const (2 : ℝ)).add hiG').add hiZ').const_mul _
  have hmR : Measurable R := correction_measurable s hU hg
  have hmM := proposalMap_measurable s hg
  have hR0 : ∀ p, 0 ≤ R p := DensityIntegrals.correction_nonneg (fun p => (flux_pos hiU hs.ne' p).le)
  have hb : ∀ p, R (proposalMap g s p) ≤ H p := fun p =>
    correction_proposal_bound hiU hs hs1 hTaylor hLip p.1 p.2
  have hiRM : Integrable (R ∘ proposalMap g s) μ := by
    refine hiH.mono' (hmR.comp hmM).aestronglyMeasurable ?_
    filter_upwards with p
    change ‖R (proposalMap g s p)‖ ≤ H p
    rw [Real.norm_eq_abs, abs_of_nonneg (hR0 _)]
    exact hb p
  have hJ : μ.map (proposalMap g s) = J := joint_density hU hg hiU hs.ne'
  have hiRJ : Integrable R J := by
    rw [← hJ]
    exact (integrable_map_measure hmR.aestronglyMeasurable hmM.aemeasurable).2 hiRM
  refine ⟨hiRJ, ?_⟩
  have he : (∫ p, R p ∂J) = ∫ p, R (proposalMap g s p) ∂μ := by
    rw [← hJ, integral_map hmM.aemeasurable hmR.aestronglyMeasurable]
  change (∫ p, R p ∂J) ≤ _
  rw [he]
  have hh := integral_mono hiRM hiH hb
  have hIH : (∫ p, H p ∂μ) = 224 * s ^ 3 *
      (2 + (∫ x, ‖g x‖ ^ 6 ∂DensityAnalysis.gibbs U) + ∫ z : Point d, ‖z‖ ^ 6 ∂stdGaussian _) := by
    dsimp [H]
    have hiA : Integrable (fun p : Point d × Point d => 2 + ‖g p.1‖ ^ 6) μ :=
      (integrable_const _).add hiG'
    rw [integral_const_mul,
      integral_add (f := fun p : Point d × Point d => 2 + ‖g p.1‖ ^ 6)
        (g := fun p => ‖p.2‖ ^ 6) hiA hiZ',
      integral_add (f := fun _ : Point d × Point d => (2 : ℝ))
        (g := fun p => ‖g p.1‖ ^ 6) (integrable_const _) hiG']
    dsimp [μ]
    rw [integral_const, integral_fun_fst (fun x : Point d => ‖g x‖ ^ 6),
      integral_fun_snd (fun x : Point d => ‖x‖ ^ 6)]
    simp only [probReal_univ, one_smul]
  rw [hIH] at hh
  exact hh.trans (by gcongr; exact GaussianMoments.norm_sixth_integral d)

theorem one_step_defect {d : ℕ} {U : Point d → ℝ} {g : Point d → Point d} {s : ℝ}
    (hU : Continuous U) (hg : Continuous g)
    (hiU : Integrable (fun x => Real.exp (-U x))) (hs : 0 < s) (hs1 : s ≤ 1)
    (hTaylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖)
    (hiG : Integrable (fun x => ‖g x‖ ^ 6) (DensityAnalysis.gibbs U))
    {f : Point d → ℝ} {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hf : ContractiveOperator.BoundedLip f B L) :
    |(∫ x, NoiseOperator.operator (stdGaussian (Point d)) (drift g (s ^ 2))
          (Real.sqrt 2 * s) f x ∂DensityAnalysis.gibbs U) - ∫ x, f x ∂DensityAnalysis.gibbs U| ≤
      L * (224 * s ^ 3 * (2 + (∫ x, ‖g x‖ ^ 6 ∂DensityAnalysis.gibbs U) +
        GaussianMoments.sixthConstant * (d : ℝ) ^ 3)) := by
  letI : IsProbabilityMeasure (DensityAnalysis.gibbs U) := gibbs_probability hiU
  let F := flux U g s
  let J := DensityIntegrals.weighted ((volume : Measure (Point d)).prod volume) F
  let μ := (DensityAnalysis.gibbs U).prod (stdGaussian (Point d))
  have hmF : Measurable F := flux_measurable s hU hg
  have hF0 : ∀ p, 0 < F p := flux_pos hiU hs.ne'
  have hJ : μ.map (proposalMap g s) = J := joint_density hU hg hiU hs.ne'
  letI : IsProbabilityMeasure J := by
    rw [← hJ]
    exact Measure.isProbabilityMeasure_map (proposalMap_measurable s hg).aemeasurable
  have hR := correction_integrable_and_bound hU hg hiU hs hs1 hTaylor hLip hiG
  have hD := DensityIntegrals.probability_defect volume hF0 hmF hR.1 hf.1 hB hL hf.2.1
    (fun x y => by simpa only [abs_sub_comm] using hf.2.2 x y)
  have hiP : Integrable (fun p : Point d × Point d => f (proposal g s p.1 p.2)) μ := by
    have hm : Measurable (fun p : Point d × Point d => f (proposal g s p.1 p.2)) :=
      hf.1.comp ((proposalMap_measurable s hg).snd)
    refine (integrable_const B).mono' hm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hf.2.1 _
  have hif : Integrable f (DensityAnalysis.gibbs U) := ContractiveOperator.bounded_integrable hf
  have hiFst : Integrable (fun p : Point d × Point d => f p.1) μ := hif.comp_fst _
  have hEq : (∫ p, f p.2 - f p.1 ∂J) =
      (∫ x, NoiseOperator.operator (stdGaussian (Point d)) (drift g (s ^ 2))
        (Real.sqrt 2 * s) f x ∂DensityAnalysis.gibbs U) - ∫ x, f x ∂DensityAnalysis.gibbs U := by
    have hm : Measurable (fun p : Point d × Point d => f p.2 - f p.1) :=
      (hf.1.comp measurable_snd).sub (hf.1.comp measurable_fst)
    rw [← hJ, integral_map (proposalMap_measurable s hg).aemeasurable hm.aestronglyMeasurable]
    change (∫ p, f (proposal g s p.1 p.2) - f p.1 ∂μ) = _
    rw [integral_sub hiP hiFst, integral_prod _ hiP, integral_fun_fst]
    simp only [probReal_univ, one_smul]
    rfl
  rw [hEq] at hD
  exact hD.trans (mul_le_mul_of_nonneg_left hR.2 hL)

end CritWinSpin.Implementation.LangevinDefect

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CritWinSpin.Implementation.LangevinConvergence

open DensityAnalysis LangevinAlgebra ContractiveOperator

theorem bernoulli_contraction {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    (1 - c) ^ n ≤ 1 / (1 + c * (n : ℝ)) := by
  have hd : 0 < 1 + c * (n : ℝ) := by positivity
  apply (le_div_iff₀ hd).2
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hs : (1 - c) * (1 + c * ((n : ℝ) + 1)) ≤ 1 + c * (n : ℝ) := by
      nlinarith [mul_nonneg (sq_nonneg c) hn]
    have hp := mul_le_mul_of_nonneg_left hs (pow_nonneg (sub_nonneg.mpr hc1) n)
    rw [pow_succ, Nat.cast_succ]
    have ih' := ih (by positivity)
    nlinarith only [hp, ih']

theorem euler_drift_lipschitz {d : ℕ} {g : Point d → Point d} {a s : ℝ}
    (ha : 0 ≤ a) (hsmall : a * s ^ 2 ≤ 1) (hstep : 16 * s ^ 2 ≤ a)
    (hmono : ∀ x y, a * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (g x - g y))
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖) :
    LipschitzWith ⟨1 - a * s ^ 2 / 2, by linarith⟩ (drift g (s ^ 2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  exact drift_contract ha (sq_nonneg _) hsmall hstep hmono hLip x y

theorem finite_time {d : ℕ} {U : Point d → ℝ} {g : Point d → Point d} {a s : ℝ}
    (hU : Continuous U) (hg : Continuous g)
    (hiU : Integrable (fun x => Real.exp (-U x)))
    (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1) (hsmall : a * s ^ 2 ≤ 1) (hstep : 16 * s ^ 2 ≤ a)
    (hmono : ∀ x y, a * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (g x - g y))
    (hTaylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖)
    (hiG : Integrable (fun x => ‖g x‖ ^ 6) (DensityAnalysis.gibbs U))
    (hiNorm : Integrable (fun x => ‖x‖) (DensityAnalysis.gibbs U))
    {f : Point d → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) (n : ℕ) :
    let P := NoiseOperator.operator (stdGaussian (Point d)) (drift g (s ^ 2)) (Real.sqrt 2 * s)
    |(P^[n] f) 0 - ∫ x, f x ∂DensityAnalysis.gibbs U| ≤
      (1 - a * s ^ 2 / 2) ^ n * L * (∫ x, ‖x‖ ∂DensityAnalysis.gibbs U) +
        (448 * L * s / a) * (2 + (∫ x, ‖g x‖ ^ 6 ∂DensityAnalysis.gibbs U) +
          GaussianMoments.sixthConstant * (d : ℝ) ^ 3) := by
  letI : IsProbabilityMeasure (DensityAnalysis.gibbs U) := gibbs_probability hiU
  let P := NoiseOperator.operator (stdGaussian (Point d)) (drift g (s ^ 2)) (Real.sqrt 2 * s)
  let q : ℝ := 1 - a * s ^ 2 / 2
  let H : ℝ := 2 + (∫ x, ‖g x‖ ^ 6 ∂DensityAnalysis.gibbs U) + GaussianMoments.sixthConstant * (d : ℝ) ^ 3
  let b := 224 * s ^ 3 * H
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; nlinarith [sq_pos_of_pos hs]
  have hb : 0 ≤ b := by
    have hg6 : 0 ≤ ∫ x, ‖g x‖ ^ 6 ∂DensityAnalysis.gibbs U := integral_nonneg fun x => by positivity
    have hc := GaussianMoments.sixth_nonneg
    dsimp [b, H]
    positivity
  have hD := euler_drift_lipschitz ha.le hsmall hstep hmono hLip
  have hP : ∀ (f : Point d → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L → BoundedLip (P f) B (q * L) := by
    intro f B L hL hf
    exact NoiseOperator.preserves_boundedLip (stdGaussian (Point d)) hD _ hL hf
  have hweak : ∀ (f : Point d → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      |(∫ x, P f x ∂DensityAnalysis.gibbs U) - ∫ x, f x ∂DensityAnalysis.gibbs U| ≤ L * b := by
    intro f B L hL hf
    have hB : 0 ≤ B := (abs_nonneg (f 0)).trans (hf.2.1 0)
    exact LangevinDefect.one_step_defect hU hg hiU hs hs1 hTaylor hLip hiG hB hL hf
  have hi : Integrable (fun x : Point d => dist 0 x) (DensityAnalysis.gibbs U) := by simpa only [dist_zero_left] using hiNorm
  have hh := from_point P q (DensityAnalysis.gibbs U) b hq hq1 hb hP hweak hL hf 0 hi n
  simp only [dist_zero_left] at hh
  have he : L * b / (1 - q) = (448 * L * s / a) * H := by
    dsimp [b, q]
    field_simp [ha.ne', hs.ne']
    ring
  rw [he] at hh
  exact hh

theorem finite_time_perturbed {d : ℕ} {U : Point d → ℝ} {g : Point d → Point d} {a s e : ℝ}
    (hU : Continuous U) (hg : Continuous g)
    (hiU : Integrable (fun x => Real.exp (-U x)))
    (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1) (he : 0 ≤ e)
    (hsmall : a * s ^ 2 ≤ 1) (hstep : 16 * s ^ 2 ≤ a)
    (hmono : ∀ x y, a * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (g x - g y))
    (hTaylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖)
    (hiG : Integrable (fun x => ‖g x‖ ^ 6) (DensityAnalysis.gibbs U))
    (hiNorm : Integrable (fun x => ‖x‖) (DensityAnalysis.gibbs U))
    (Q : (Point d → ℝ) → Point d → ℝ)
    (hQ : ∀ (f : Point d → ℝ) (B : ℝ), Measurable f → (∀ x, |f x| ≤ B) →
      Measurable (Q f) ∧ ∀ x, |Q f x| ≤ B)
    (hQC : ∀ (f g : Point d → ℝ) (B D : ℝ), Measurable f → Measurable g →
      (∀ x, |f x| ≤ B) → (∀ x, |g x| ≤ B) → (∀ x, |f x - g x| ≤ D) →
      ∀ x, |Q f x - Q g x| ≤ D)
    (happrox : ∀ (f : Point d → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      ∀ x, |Q f x - NoiseOperator.operator (stdGaussian (Point d)) (drift g (s ^ 2))
        (Real.sqrt 2 * s) f x| ≤ L * e)
    {f : Point d → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) (n : ℕ) :
    |(Q^[n] f) 0 - ∫ x, f x ∂DensityAnalysis.gibbs U| ≤
      (1 - a * s ^ 2 / 2) ^ n * L * (∫ x, ‖x‖ ∂DensityAnalysis.gibbs U) +
        (448 * L * s / a) * (2 + (∫ x, ‖g x‖ ^ 6 ∂DensityAnalysis.gibbs U) +
          GaussianMoments.sixthConstant * (d : ℝ) ^ 3) + 2 * L * e / (a * s ^ 2) := by
  let P := NoiseOperator.operator (stdGaussian (Point d)) (drift g (s ^ 2)) (Real.sqrt 2 * s)
  let q : ℝ := 1 - a * s ^ 2 / 2
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; nlinarith [sq_pos_of_pos hs]
  have hD := euler_drift_lipschitz ha.le hsmall hstep hmono hLip
  have hP : ∀ (f : Point d → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L → BoundedLip (P f) B (q * L) := by
    intro f B L hL hf
    exact NoiseOperator.preserves_boundedLip (stdGaussian (Point d)) hD _ hL hf
  have hpert := perturbed_iterates P q e hq he hP hQ hQC happrox hL hf n 0
  have hsum := mul_le_mul_of_nonneg_left (geometric_sum_bound q hq hq1 n) (mul_nonneg hL he)
  have hPure := finite_time hU hg hiU ha hs hs1 hsmall hstep hmono hTaylor hLip hiG hiNorm hL hf n
  change |(P^[n] f) 0 - ∫ x, f x ∂DensityAnalysis.gibbs U| ≤ _ at hPure
  have ht := abs_sub_le ((Q^[n] f) 0) ((P^[n] f) 0) (∫ x, f x ∂DensityAnalysis.gibbs U)
  have hEq : L * e * (1 / (1 - q)) = 2 * L * e / (a * s ^ 2) := by dsimp [q]; field_simp; ring
  rw [hEq] at hsum
  linarith

end CritWinSpin.Implementation.LangevinConvergence

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp
open scoped BigOperators

namespace CritWinSpin.Implementation.KernelTests

variable {A X : Type*} [Fintype A]

def test (K : X → A → ℝ) (w : A → ℝ) (x : X) : ℝ := ∑ a, w a * K x a

theorem test_bound {K : X → A → ℝ} (hK : ∀ x, IsDistribution (K x))
    {w : A → ℝ} (hw : ∀ a, |w a| ≤ 1) (x : X) : |test K w x| ≤ 1 := by
  calc
    _ ≤ ∑ a, |w a * K x a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, K x a := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg ((hK x).1 a)]
      exact (mul_le_mul_of_nonneg_right (hw a) ((hK x).1 a)).trans_eq (one_mul _)
    _ = 1 := (hK x).2

theorem test_difference {K : X → A → ℝ} {w : A → ℝ} (hw : ∀ a, |w a| ≤ 1) (x y : X) :
    |test K w x - test K w y| ≤ 2 * tvDist (K x) (K y) := by
  have he : test K w x - test K w y = ∑ a, w a * (K x a - K y a) := by
    simp only [test, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ a, |w a * (K x a - K y a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |K x a - K y a| := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hw a) (abs_nonneg _)).trans_eq (one_mul _)
    _ = _ := by unfold tvDist; ring

theorem test_measurable [MeasurableSpace X] {K : X → A → ℝ}
    (hK : ∀ a, Measurable (fun x => K x a)) (w : A → ℝ) : Measurable (test K w) := by
  exact Finset.measurable_sum _ fun a _ => (hK a).const_mul (w a)

theorem test_boundedLip [PseudoMetricSpace X] [MeasurableSpace X]
    {K : X → A → ℝ} (hK : ∀ x, IsDistribution (K x))
    (hmK : ∀ a, Measurable (fun x => K x a)) {C : ℝ}
    (hLip : ∀ x y, tvDist (K x) (K y) ≤ C * dist x y)
    {w : A → ℝ} (hw : ∀ a, |w a| ≤ 1) :
    ContractiveOperator.BoundedLip (test K w) 1 (2 * C) := by
  refine ⟨test_measurable hmK w, test_bound hK hw, ?_⟩
  intro x y
  exact (test_difference hw x y).trans (by linarith [hLip x y])

theorem tv_of_tests {P Q : A → ℝ} {E : ℝ}
    (htest : ∀ w : A → ℝ, (∀ a, |w a| ≤ 1) → |∑ a, w a * (P a - Q a)| ≤ E) :
    tvDist P Q ≤ E / 2 := by
  classical
  let w : A → ℝ := fun a => if 0 ≤ P a - Q a then 1 else -1
  have hw : ∀ a, |w a| ≤ 1 := by intro a; dsimp [w]; split_ifs <;> norm_num
  have he : ∑ a, w a * (P a - Q a) = ∑ a, |P a - Q a| := by
    apply Finset.sum_congr rfl
    intro a _
    dsimp [w]
    split_ifs with ha
    · rw [one_mul, abs_of_nonneg ha]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge ha)]
  have hh := htest w hw
  rw [he, abs_of_nonneg (Finset.sum_nonneg fun a _ => abs_nonneg _)] at hh
  unfold tvDist
  linarith

theorem coordinate_integrable [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {K : X → A → ℝ} (hK : ∀ x, IsDistribution (K x))
    (hmK : ∀ a, Measurable (fun x => K x a)) (a : A) : Integrable (fun x => K x a) μ := by
  refine (integrable_const (1 : ℝ)).mono' (hmK a).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg ((hK x).1 a)]
  exact (Finset.single_le_sum (fun b _ => (hK x).1 b) (Finset.mem_univ a)).trans_eq (hK x).2

theorem integral_test [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {K : X → A → ℝ} (hK : ∀ x, IsDistribution (K x))
    (hmK : ∀ a, Measurable (fun x => K x a)) (w : A → ℝ) :
    (∫ x, test K w x ∂μ) = ∑ a, w a * ∫ x, K x a ∂μ := by
  unfold test
  rw [integral_finsetSum _ fun a _ => (coordinate_integrable μ hK hmK a).const_mul (w a)]
  simp only [integral_const_mul]

theorem mixture_tv [PseudoMetricSpace X] [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : X → A → ℝ} (hK : ∀ x, IsDistribution (K x))
    (hmK : ∀ a, Measurable (fun x => K x a)) {C E : ℝ}
    (hLip : ∀ x y, tvDist (K x) (K y) ≤ C * dist x y)
    (hweak : ∀ f : X → ℝ, ContractiveOperator.BoundedLip f 1 (2 * C) →
      |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ E) :
    tvDist (fun a => ∫ x, K x a ∂μ) (fun a => ∫ x, K x a ∂ν) ≤ E / 2 := by
  apply tv_of_tests
  intro w hw
  have hh := hweak (test K w) (test_boundedLip hK hmK hLip hw)
  rw [integral_test μ hK hmK, integral_test ν hK hmK] at hh
  simpa only [mul_sub, Finset.sum_sub_distrib] using hh

end CritWinSpin.Implementation.KernelTests

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace CritWinSpin.Implementation.LangevinBudget
open DensityAnalysis LangevinAlgebra ContractiveOperator LangevinConvergence

structure Certificate (d : ℕ) (a : ℝ) where
  U : Point d → ℝ
  g : Point d → Point d
  continuous_U : Continuous U
  continuous_g : Continuous g
  density_integrable : Integrable (fun x => Real.exp (-U x))
  monotone : ∀ x y, a * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (g x - g y)
  taylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2
  lipschitz : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖
  grad_integrable : Integrable (fun x => ‖g x‖ ^ 6) (DensityAnalysis.gibbs U)
  norm_integrable : Integrable (fun x => ‖x‖) (DensityAnalysis.gibbs U)

theorem arithmetic_bound {R a s e L M H : ℝ} {n : ℕ}
    (hR : 2 ≤ R) (ha : 0 < a) (haR : 1 ≤ a * R)
    (hs : 0 < s) (hsmall : a * s ^ 2 ≤ 1)
    (hsR : s ≤ 1 / (2048 * R ^ 4))
    (he : e ≤ s ^ 2 / (16 * R ^ 3))
    (hn : 16 * R ^ 4 / s ^ 2 ≤ (n : ℝ))
    (hL : 0 ≤ L) (hLR : L ≤ R) (hM : 0 ≤ M) (hMR : M ≤ R)
    (hH : 0 ≤ H) (hHR : H ≤ R) :
    (1 - a * s ^ 2 / 2) ^ n * L * M + (448 * L * s / a) * H +
      2 * L * e / (a * s ^ 2) ≤ 1 / (2 * R) := by
  have hRp : 0 < R := by linarith
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have haInv : 1 / a ≤ R := (div_le_iff₀ ha).2 (by nlinarith only [haR])
  have hCn : 8 * R ^ 3 ≤ (a * s ^ 2 / 2) * (n : ℝ) := by
    have hn' := (div_le_iff₀ hs2).1 hn
    have h₁ := mul_le_mul_of_nonneg_left hn' (show 0 ≤ a / 2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right haR (show 0 ≤ 8 * R ^ 3 by positivity)
    nlinarith only [h₁, h₂]
  have hPow : (1 - a * s ^ 2 / 2) ^ n ≤ 1 / (8 * R ^ 3) :=
    (bernoulli_contraction (by positivity : 0 ≤ a * s ^ 2 / 2) (by linarith only [hsmall]) n).trans
      (one_div_le_one_div_of_le (by positivity) (by linarith only [hCn]))
  have hLM : L * M ≤ R ^ 2 := by nlinarith [mul_le_mul hLR hMR hM (by positivity : 0 ≤ R)]
  have hLH : L * H ≤ R ^ 2 := by nlinarith [mul_le_mul hLR hHR hH (by positivity : 0 ≤ R)]
  have hMix : (1 - a * s ^ 2 / 2) ^ n * L * M ≤ 1 / (8 * R) := by
    calc
      _ ≤ (1 / (8 * R ^ 3)) * (L * M) := by
        have ht := mul_le_mul_of_nonneg_right hPow (mul_nonneg hL hM)
        nlinarith only [ht]
      _ ≤ (1 / (8 * R ^ 3)) * R ^ 2 := mul_le_mul_of_nonneg_left hLM (by positivity)
      _ = _ := by field_simp [hRp.ne'] <;> ring
  have hBias : (448 * L * s / a) * H ≤ 7 / (32 * R) := by
    have hid : (448 * L * s / a) * H = 448 * s * (L * H) * (1 / a) := by ring
    rw [hid]
    calc
      _ ≤ 448 * (1 / (2048 * R ^ 4)) * R ^ 2 * R := by
        apply mul_le_mul _ haInv (by positivity) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hsR (by norm_num)) hLH
          (mul_nonneg hL hH) (by positivity)
      _ = _ := by field_simp [hRp.ne'] <;> ring
  have hRound : 2 * L * e / (a * s ^ 2) ≤ 1 / (8 * R) := by
    have ht := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * L))
      (by positivity : 0 ≤ a * s ^ 2)
    have hid : 2 * L * (s ^ 2 / (16 * R ^ 3)) / (a * s ^ 2) =
        L * (1 / a) / (8 * R ^ 3) := by field_simp [ha.ne', hs.ne', hRp.ne'] <;> ring
    rw [hid] at ht
    calc
      _ ≤ L * (1 / a) / (8 * R ^ 3) := ht
      _ ≤ R ^ 2 / (8 * R ^ 3) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hm := mul_le_mul hLR haInv (by positivity : 0 ≤ 1 / a) (by positivity : 0 ≤ R)
        nlinarith only [hm]
      _ = _ := by field_simp [hRp.ne'] <;> ring
  have hsum : 1 / (8 * R) + 7 / (32 * R) + 1 / (8 * R) ≤ 1 / (2 * R) := by
    have hid : 1 / (8 * R) + 7 / (32 * R) + 1 / (8 * R) = 15 / (32 * R) := by
      field_simp [hRp.ne'] <;> ring
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0 < 32 * R) (by positivity : 0 < 2 * R)).2
    nlinarith only [hRp]
  linarith only [hMix, hBias, hRound, hsum]

theorem schedule_admissible {R a s : ℝ} (hR : 2 ≤ R) (ha1 : a ≤ 1)
    (haR : 1 ≤ a * R) (hs : 0 < s) (hsR : s ≤ 1 / (2048 * R ^ 4)) :
    s ≤ 1 ∧ a * s ^ 2 ≤ 1 ∧ 16 * s ^ 2 ≤ a := by
  have hRp : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR1
  have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR1
  have hdeg : R ≤ R ^ 4 := by
    have hh := mul_le_mul_of_nonneg_left hR3 hRp.le
    nlinarith only [hh]
  have hs1 : s ≤ 1 := hsR.trans
    ((div_le_one (by positivity : 0 < 2048 * R ^ 4)).2 (by nlinarith only [hR4]))
  have hs2 : s ^ 2 ≤ 1 := by nlinarith only [hs.le, hs1]
  have hs16 : 16 * s * R ≤ 1 := by
    calc
      _ = s * (16 * R) := by ring
      _ ≤ (1 / (2048 * R ^ 4)) * (16 * R) :=
        mul_le_mul_of_nonneg_right hsR (by positivity)
      _ = (16 * R) / (2048 * R ^ 4) := by ring
      _ ≤ 1 := (div_le_one (by positivity : 0 < 2048 * R ^ 4)).2
        (by nlinarith only [hdeg, hRp])
  have hs16sq : (16 * s ^ 2) * R ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hs1 (show 0 ≤ 16 * s * R by positivity)
    nlinarith only [hh, hs16]
  refine ⟨hs1, ?_, le_of_mul_le_mul_right (hs16sq.trans haR) hRp⟩
  exact (mul_le_mul_of_nonneg_right ha1 (sq_nonneg s)).trans (by simpa only [one_mul] using hs2)

theorem weak_bound {d : ℕ} {a s e R : ℝ} (cert : Certificate d a)
    (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1) (he0 : 0 ≤ e)
    (hsmall : a * s ^ 2 ≤ 1) (hstep : 16 * s ^ 2 ≤ a)
    (hR : 2 ≤ R) (haR : 1 ≤ a * R) (hsR : s ≤ 1 / (2048 * R ^ 4))
    (he : e ≤ s ^ 2 / (16 * R ^ 3))
    (hM : (∫ x, ‖x‖ ∂DensityAnalysis.gibbs cert.U) ≤ R)
    (hH : 2 + (∫ x, ‖cert.g x‖ ^ 6 ∂DensityAnalysis.gibbs cert.U) +
      GaussianMoments.sixthConstant * (d : ℝ) ^ 3 ≤ R)
    (Q : (Point d → ℝ) → Point d → ℝ)
    (hQ : ∀ (f : Point d → ℝ) (B : ℝ), Measurable f → (∀ x, |f x| ≤ B) →
      Measurable (Q f) ∧ ∀ x, |Q f x| ≤ B)
    (hQC : ∀ (f g : Point d → ℝ) (B D : ℝ), Measurable f → Measurable g →
      (∀ x, |f x| ≤ B) → (∀ x, |g x| ≤ B) → (∀ x, |f x - g x| ≤ D) →
      ∀ x, |Q f x - Q g x| ≤ D)
    (happrox : ∀ (f : Point d → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      ∀ x, |Q f x - NoiseOperator.operator (stdGaussian (Point d)) (drift cert.g (s ^ 2))
        (Real.sqrt 2 * s) f x| ≤ L * e)
    {f : Point d → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hLR : L ≤ R) (hf : BoundedLip f B L)
    (n : ℕ) (hn : 16 * R ^ 4 / s ^ 2 ≤ (n : ℝ)) :
    |(Q^[n] f) 0 - ∫ x, f x ∂DensityAnalysis.gibbs cert.U| ≤ 1 / (2 * R) := by
  have ht := finite_time_perturbed cert.continuous_U cert.continuous_g cert.density_integrable
    ha hs hs1 he0 hsmall hstep cert.monotone cert.taylor cert.lipschitz
    cert.grad_integrable cert.norm_integrable Q hQ hQC happrox hL hf n
  apply ht.trans
  exact arithmetic_bound hR ha haR hs hsmall hsR he hn hL hLR
    (integral_nonneg (fun x => norm_nonneg x)) hM
    (by have hc := GaussianMoments.sixth_nonneg; positivity) hH

end CritWinSpin.Implementation.LangevinBudget
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- Finite-precision Langevin weak approximation with an explicit polynomial budget. -/
theorem solution (d : ℕ) (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (hμ : μ = ((∫⁻ x : EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal (Real.exp (-U x)) ∂volume)⁻¹) •
      (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-U x))))
    (a s e R : ℝ)
    (hU : Continuous U) (hg : Continuous g)
    (hiU : Integrable (fun x => Real.exp (-U x)))
    (hmono : ∀ x y, a * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (g x - g y))
    (hTaylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖)
    (hiG : Integrable (fun x => ‖g x‖ ^ 6) μ)
    (hiNorm : Integrable (fun x => ‖x‖) μ)
    (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1) (he0 : 0 ≤ e)
    (hsmall : a * s ^ 2 ≤ 1) (hstep : 16 * s ^ 2 ≤ a)
    (hR : 2 ≤ R) (haR : 1 ≤ a * R) (hsR : s ≤ 1 / (2048 * R ^ 4))
    (he : e ≤ s ^ 2 / (16 * R ^ 3))
    (hM : (∫ x, ‖x‖ ∂μ) ≤ R)
    (hH : 2 + (∫ x, ‖g x‖ ^ 6 ∂μ) +
      (∫ t : ℝ, |t| ^ 6 ∂gaussianReal 0 1) * (d : ℝ) ^ 3 ≤ R)
    (Q : (EuclideanSpace ℝ (Fin d) → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ)
    (hQ : ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (B : ℝ),
      Measurable f → (∀ x, |f x| ≤ B) → Measurable (Q f) ∧ ∀ x, |Q f x| ≤ B)
    (hQC : ∀ (f k : EuclideanSpace ℝ (Fin d) → ℝ) (B D : ℝ),
      Measurable f → Measurable k → (∀ x, |f x| ≤ B) → (∀ x, |k x| ≤ B) →
      (∀ x, |f x - k x| ≤ D) → ∀ x, |Q f x - Q k x| ≤ D)
    (happrox : ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (B L : ℝ), 0 ≤ L →
      Measurable f → (∀ x, |f x| ≤ B) → (∀ x y, |f x - f y| ≤ L * dist x y) →
      ∀ x, |Q f x - ∫ z, f (x - s ^ 2 • g x + (Real.sqrt 2 * s) • z)
        ∂stdGaussian (EuclideanSpace ℝ (Fin d))| ≤ L * e)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (B L : ℝ)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hf : Measurable f)
    (hfB : ∀ x, |f x| ≤ B) (hfL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (n : ℕ) (hn : 16 * R ^ 4 / s ^ 2 ≤ (n : ℝ)) :
    |(Q^[n] f) 0 - ∫ x, f x ∂μ| ≤ 1 / (2 * R) := by
  subst μ
  let cert : CritWinSpin.Implementation.LangevinBudget.Certificate d a := {
    U := U
    g := g
    continuous_U := hU
    continuous_g := hg
    density_integrable := hiU
    monotone := hmono
    taylor := hTaylor
    lipschitz := hLip
    grad_integrable := hiG
    norm_integrable := hiNorm }
  have hA : ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ) (B L : ℝ), 0 ≤ L →
      CritWinSpin.Implementation.ContractiveOperator.BoundedLip v B L →
      ∀ x, |Q v x - CritWinSpin.Implementation.NoiseOperator.operator
        (stdGaussian (EuclideanSpace ℝ (Fin d)))
        (CritWinSpin.Implementation.LangevinAlgebra.drift g (s ^ 2))
        (Real.sqrt 2 * s) v x| ≤ L * e := by
    intro v B L hL hv x
    exact happrox v B L hL hv.1 hv.2.1 hv.2.2 x
  exact CritWinSpin.Implementation.LangevinBudget.weak_bound cert
    ha hs hs1 he0 hsmall hstep hR haR hsR he hM hH Q hQ hQC hA hL hLR ⟨hf,hfB,hfL⟩ n hn

#print axioms solution

end
end
