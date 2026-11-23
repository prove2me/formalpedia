-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.gammaIntegral_gaussian_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:27:41.290224+00:00
-- url     : https://prove2.me/submissions/71ccf6a1-befa-4b18-9183-204be17e9730

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


section
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
namespace DedekindZeta.GammaIntegral
open Classical
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
private theorem ofReal_prod_cpow {ι : Type*} (t : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ t, 0 ≤ g i) (s : ℂ) :
    (((∏ i ∈ t, g i : ℝ)) : ℂ) ^ s = ∏ i ∈ t, ((g i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (hg a (Finset.mem_insert_self a t))
          (Finset.prod_nonneg fun i hi => hg i (Finset.mem_insert_of_mem hi)),
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]
private theorem ofReal_sq_cpow {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (((r ^ 2 : ℝ)) : ℂ) ^ s = (r : ℂ) ^ (2 * s) := by
  have him : (Complex.log (r : ℂ) * 2).im = 0 := by
    simp [Complex.mul_im, Complex.log_im, Complex.arg_ofReal_of_nonneg hr.le]
  rw [Complex.cpow_mul (x := (r : ℂ)) (y := 2) s
      (by rw [him]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [him]; exact Real.pi_pos.le), Complex.cpow_two, ← Complex.ofReal_pow]
end
end DedekindZeta.GammaIntegral
namespace DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
end
end DedekindZeta
namespace DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped nonZeroDivisors
end
end DedekindZeta.GammaIntegral
end

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open Classical
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ) :
    gammaIntegral K (fun x => (gaussian K x : ℂ)) s =
      (∫ y : {w : InfinitePlace K // IsReal w} → ℝ, ∏ w, realFactor s (y w)) *
        (∫ y : {w : InfinitePlace K // IsComplex w} → ℂ, ∏ w, complexFactor s (y w)) := by
  classical
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Measurability of the `mulHaar` density, for pushing it into the integrand.
  have hmeas : AEMeasurable (fun x : mixedEmbedding.mixedSpace K =>
      ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹)) volume :=
    (ENNReal.measurable_ofReal.comp
      (measurable_const.mul
        (Measurable.inv (mixedEmbedding.continuous_norm (K := K)).measurable))).aemeasurable
  -- The two product integrands, separated.
  set F : ({w : InfinitePlace K // IsReal w} → ℝ) → ℂ :=
    fun y => ∏ w, realFactor s (y w) with hF
  set G : ({w : InfinitePlace K // IsComplex w} → ℂ) → ℂ :=
    fun y => ∏ w, complexFactor s (y w) with hG
  -- The pointwise identity for the pushed-density integrand.
  have key : ∀ x : mixedEmbedding.mixedSpace K,
      (ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K *
          (mixedEmbedding.norm x)⁻¹)).toReal •
        ((gaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
        = F x.1 * G x.2 := by
    intro x
    by_cases hx0 : mixedEmbedding.norm x = 0
    · -- On the zero locus both sides vanish.
      have hLHS : (ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K *
          (mixedEmbedding.norm x)⁻¹)).toReal •
          ((gaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s) = 0 := by
        rw [hx0, inv_zero, mul_zero, ENNReal.ofReal_zero, ENNReal.toReal_zero, zero_smul]
      rw [hLHS]
      obtain ⟨w, hw⟩ := mixedEmbedding.norm_eq_zero_iff.mp hx0
      symm
      obtain hwr | hwc := isReal_or_isComplex w
      · have : F x.1 = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ (⟨w, hwr⟩ :
            {w : InfinitePlace K // IsReal w})) ?_
          have hzero : x.1 ⟨w, hwr⟩ = 0 := by
            have := normAtPlace_apply_of_isReal hwr x
            rw [hw] at this
            simpa using (norm_eq_zero.mp this.symm)
          simp [realFactor, hzero]
        rw [this, zero_mul]
      · have : G x.2 = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ (⟨w, hwc⟩ :
            {w : InfinitePlace K // IsComplex w})) ?_
          have hzero : x.2 ⟨w, hwc⟩ = 0 := by
            have := normAtPlace_apply_of_isComplex hwc x
            rw [hw] at this
            simpa using (norm_eq_zero.mp this.symm)
          simp [complexFactor, hzero]
        rw [this, mul_zero]
    · -- Away from the zero locus: every place-norm is positive.
      have hpos : ∀ w : InfinitePlace K, normAtPlace w x ≠ 0 := fun w hw =>
        hx0 (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, hw⟩)
      have hnn : (0 : ℝ) ≤ (2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹ :=
        mul_nonneg (by positivity) (inv_nonneg.mpr (mixedEmbedding.norm_nonneg x))
      -- Split each place-product into its three constituent factors.
      have hF_split : F x.1 =
          (∏ w : {w : InfinitePlace K // IsReal w}, ((|x.1 w|⁻¹ : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsReal w},
            ((Real.exp (-Real.pi * (x.1 w) ^ 2) : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsReal w}, ((|x.1 w| : ℝ) : ℂ) ^ s) := by
        rw [hF, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [realFactor, Complex.real_smul]; push_cast; ring
      have hG_split : G x.2 =
          (∏ w : {w : InfinitePlace K // IsComplex w},
            ((2 / Real.pi * (‖x.2 w‖ ^ 2)⁻¹ : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsComplex w},
            ((Real.exp (-2 * Real.pi * ‖x.2 w‖ ^ 2) : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsComplex w}, ((‖x.2 w‖ : ℝ) : ℂ) ^ (2 * s)) := by
        rw [hG, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [complexFactor, Complex.real_smul]; push_cast; ring
      -- Bracket 1: the density factor.
      have hB1 :
          (∏ w : {w : InfinitePlace K // IsReal w}, ((|x.1 w|⁻¹ : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsComplex w},
            ((2 / Real.pi * (‖x.2 w‖ ^ 2)⁻¹ : ℝ) : ℂ))
          = (((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
          Complex.ofReal_inj]
        have hnorm : mixedEmbedding.norm x =
            (∏ w : {w : InfinitePlace K // IsReal w}, |x.1 w|) *
            (∏ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2) := by
          rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod]
          congr 1
          · refine Finset.prod_congr rfl fun w _ => ?_
            rw [mult_isReal, normAtPlace_apply_of_isReal w.2, pow_one, Real.norm_eq_abs]
          · refine Finset.prod_congr rfl fun w _ => ?_
            rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2]
        have hconst : (∏ _w : {w : InfinitePlace K // IsComplex w}, (2 / Real.pi : ℝ))
            = (2 / Real.pi) ^ nrComplexPlaces K := by
          rw [Finset.prod_const, Finset.card_univ]
        rw [hnorm]
        simp only [Finset.prod_inv_distrib, Finset.prod_mul_distrib, hconst, mul_inv]
        ring
      -- Bracket 2: the Gaussian.
      have hB2 :
          (∏ w : {w : InfinitePlace K // IsReal w},
            ((Real.exp (-Real.pi * (x.1 w) ^ 2) : ℝ) : ℂ)) *
          (∏ w : {w : InfinitePlace K // IsComplex w},
            ((Real.exp (-2 * Real.pi * ‖x.2 w‖ ^ 2) : ℝ) : ℂ))
          = (gaussian K x : ℂ) := by
        rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
          Complex.ofReal_inj]
        rw [gaussian, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
        congr 1
        rw [sum_eq_sum_add_sum, mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun w _ => ?_
          rw [mult_isReal, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs, sq_abs]
          push_cast; ring
        · refine Finset.sum_congr rfl fun w _ => ?_
          rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2]
          push_cast; ring
      -- Bracket 3: the norm power.
      have hB3 :
          (∏ w : {w : InfinitePlace K // IsReal w}, ((|x.1 w| : ℝ) : ℂ) ^ s) *
          (∏ w : {w : InfinitePlace K // IsComplex w}, ((‖x.2 w‖ : ℝ) : ℂ) ^ (2 * s))
          = (mixedEmbedding.norm x : ℂ) ^ s := by
        rw [mixedEmbedding.norm_apply,
          ofReal_prod_cpow Finset.univ (fun w => normAtPlace w x ^ mult w)
            (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _) s,
          prod_eq_prod_mul_prod]
        congr 1
        · refine Finset.prod_congr rfl fun w _ => ?_
          rw [mult_isReal, normAtPlace_apply_of_isReal w.2, pow_one, Real.norm_eq_abs]
        · refine Finset.prod_congr rfl fun w _ => ?_
          have hposc : ‖x.2 ⟨w.1, w.2⟩‖ ≠ 0 := by
            have := hpos w.1; rwa [normAtPlace_apply_of_isComplex w.2] at this
          rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2,
            ofReal_sq_cpow ((norm_nonneg _).lt_of_ne hposc.symm) s]
      -- Assemble.
      rw [ENNReal.toReal_ofReal hnn, Complex.real_smul, hF_split, hG_split,
        show ((((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹ : ℝ) : ℂ)) *
            ((gaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
          = ((((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹ : ℝ) : ℂ)) *
            ((gaussian K x : ℂ)) * ((mixedEmbedding.norm x : ℂ) ^ s) from by ring,
        ← hB1, ← hB2, ← hB3]
      ring
  -- Now compute the integral.
  rw [gammaIntegral, mulHaar, integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _,
    integral_congr_ae (Filter.Eventually.of_forall key), Measure.volume_eq_prod,
    integral_prod_mul F G]
end DedekindZeta.GammaIntegral
