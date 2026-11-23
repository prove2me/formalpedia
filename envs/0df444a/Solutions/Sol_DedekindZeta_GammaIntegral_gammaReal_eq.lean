-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.gammaReal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:26:09.505976+00:00
-- url     : https://prove2.me/submissions/3de21a43-dea4-457b-adb5-cc0ddf9acf0a

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
open scoped Real in
/-- Complex-valued analogue of `MeasureTheory.integral_comp_abs`: the Lebesgue
integral over `ℝ` of an even-by-construction integrand `f |x|` is twice the
half-line integral.  (Mathlib's `integral_comp_abs` is stated only for
`f : ℝ → ℝ`; we need the `ℂ`-valued version for the Gaussian Mellin integrand.) -/
private theorem integral_comp_abs_complex {f : ℝ → ℂ} :
    ∫ x, f |x| = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
  have eq : ∫ x : ℝ in Set.Ioi 0, f |x| = ∫ x : ℝ in Set.Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_of_pos hx]
  by_cases hf : IntegrableOn (fun x => f |x|) (Set.Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Set.Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Set.Iic 0, f |x|) + ∫ x in Set.Ioi 0, f |x| := by
        rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Set.Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ x in Set.Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_of_nonpos hx]
  · have hni : ¬ Integrable (fun x => f |x|) := by
      exact fun h => hf h.integrableOn
    rw [← eq, integral_undef hf, integral_undef hni, mul_zero]
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
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) :
    gammaReal s = DedekindZeta.LReal s := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Step 1: replace the multiplicative-density integral by a plain Lebesgue integral.
  have hmeas : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal |x|⁻¹) volume := by
    apply Measurable.aemeasurable
    exact ENNReal.measurable_ofReal.comp ((measurable_id.norm).inv)
  rw [gammaReal,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  -- Step 2: rewrite the integrand as `H |x|` for `H t = t⁻¹ • (e^{-πt²} (↑t)^s)`.
  set H : ℝ → ℂ := fun t : ℝ =>
    (t⁻¹ : ℝ) • ((Real.exp (-Real.pi * t ^ 2) : ℂ) * (t : ℂ) ^ s) with hH
  have hrw : (∫ x : ℝ, (ENNReal.ofReal |x|⁻¹).toReal •
        ((Real.exp (-Real.pi * x ^ 2) : ℂ) * ((|x| : ℝ) : ℂ) ^ s))
      = ∫ x : ℝ, H |x| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hH, ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x))]
    rw [← sq_abs x]
  rw [hrw, integral_comp_abs_complex]
  -- Step 3: identify the half-line integral with the Mellin transform of the Gaussian.
  have hHalf : (∫ t in Set.Ioi (0 : ℝ), H t)
      = mellin (fun t => (Real.exp (-Real.pi * t ^ 2) : ℂ)) s := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Set.mem_Ioi] at ht
    simp only [hH]
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    rw [Complex.real_smul, Complex.ofReal_inv, smul_eq_mul,
      Complex.cpow_sub _ _ ht0, Complex.cpow_one]
    field_simp
  rw [hHalf]
  -- Step 4: evaluate the Mellin transform of the Gaussian via `mellin_comp_rpow`.
  have hgauss : mellin (fun t => (Real.exp (-Real.pi * t ^ 2) : ℂ)) s
      = mellin (fun t => (Real.exp (-Real.pi * t ^ (2 : ℝ)) : ℂ)) s := by
    rw [mellin, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Set.mem_Ioi] at ht
    congr 2
    rw [← Real.rpow_natCast t 2]
    norm_num
  rw [hgauss]
  have hcomp := mellin_comp_rpow (fun u => (Real.exp (-Real.pi * u) : ℂ)) s 2
  rw [hcomp, show (s / ((2 : ℝ) : ℂ)) = s / 2 by push_cast; ring]
  -- Step 5: the one-variable Gaussian Mellin transform is `(1/π)^{s/2} Γ(s/2)`.
  have hmf : mellin (fun u => (Real.exp (-Real.pi * u) : ℂ)) (s / 2)
      = (1 / Real.pi) ^ (s / 2) * Complex.Gamma (s / 2) := by
    rw [mellin]
    rw [show (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s / 2 - 1) •
          (Real.exp (-Real.pi * t) : ℂ))
        = ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s / 2 - 1) *
          Complex.exp (-(Real.pi * t)) from ?_]
    · rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi (by simpa using hs) hπ]
    · refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [smul_eq_mul]
      congr 1
      rw [Complex.ofReal_exp]
      congr 1
      push_cast; ring
  rw [hmf]
  -- Step 6: bookkeep the constants and match `LReal`.
  rw [DedekindZeta.LReal, Complex.real_smul]
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hπ.le]; exact hπ.ne
  rw [show ((|(2 : ℝ)|⁻¹ : ℝ) : ℂ) = 1 / 2 by norm_num]
  rw [one_div (Real.pi : ℂ), Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  rw [show (-s / 2 : ℂ) = -(s / 2) by ring]
  ring
end DedekindZeta.GammaIntegral
