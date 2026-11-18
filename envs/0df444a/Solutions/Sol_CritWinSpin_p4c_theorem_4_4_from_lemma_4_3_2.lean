-- Prove2me | solution 2 for CritWinSpin.p4c_theorem_4_4_from_lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Maxliu
-- created : 2026-11-17T18:40:21.327408+00:00
-- url     : https://prove2.me/submissions/1ebafbae-f38d-466a-903e-35c02e93985c

import Definitions.Def_CritWinSpin_SamplerMachine
import Theorems.Thm_CritWinSpin_regularized_envelope_budget
import Theorems.Thm_CritWinSpin_rounded_euler_weak_budget
import Theorems.Thm_CritWinSpin_numeric_kernel_trajectory_tv
import Theorems.Thm_CritWinSpin_Implementation_SamplerRuntime_criticalWindowMachine_time
import Theorems.Thm_CritWinSpin_LocalTM2_Compiled_sampler_retry_law
import Theorems.Thm_CritWinSpin_p4c_4_4_math

set_option linter.all false


section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.DensityAnalysis















namespace EulerDensity
open ProbabilityTheory MeasureTheory WithLp
open scoped ENNReal NNReal RealInnerProductSpace















end EulerDensity

namespace EulerDensity
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace













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




























end CritWinSpin.Implementation.MetropolisFlux

end

section

set_option autoImplicit false
open scoped RealInnerProductSpace
noncomputable section

namespace CritWinSpin.Implementation.LangevinAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]





























end CritWinSpin.Implementation.LangevinAlgebra

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.DensityIntegrals

variable {Ω : Type*} [MeasurableSpace Ω]









variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]









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



















end CritWinSpin.Implementation.LangevinJointDensity

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace CritWinSpin.Implementation.GaussianMoments



















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



variable (P : (E → ℝ) → E → ℝ) (q : ℝ)















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









end CritWinSpin.Implementation.LangevinBudget
end

end

section

open MeasureTheory IsingLTL.BeliefProp

set_option autoImplicit false
set_option maxHeartbeats 2400000

open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeAnalysis

section SpinAndPhi

noncomputable def mgf (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))

theorem mgf_pos (S : SpinLaw) (t : ℝ) : 0 < mgf S t := by
  unfold mgf
  have hmem : (1 : ℚ) ∈ S.A := S.one_mem
  have hterm : 0 < (S.ρ (1 : ℚ) : ℝ) * Real.exp (t * ((1 : ℚ) : ℝ)) := by
    have hρ : 0 < (S.ρ 1 : ℝ) := by exact_mod_cast S.pos 1 hmem
    positivity
  have hnn : ∀ x ∈ S.A, 0 ≤ (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := fun x hx => by
    have : 0 < (S.ρ x : ℝ) := by exact_mod_cast S.pos x hx
    positivity
  exact lt_of_lt_of_le hterm (Finset.single_le_sum hnn hmem)

theorem mgf_zero (S : SpinLaw) : mgf S 0 = 1 := by
  unfold mgf
  simp only [zero_mul, Real.exp_zero, mul_one]
  exact_mod_cast S.sum_one

theorem mgf_even (S : SpinLaw) (t : ℝ) : mgf S (-t) = mgf S t := by
  unfold mgf
  refine Finset.sum_equiv (Equiv.neg ℚ) ?_ ?_
  · intro x
    simp only [Equiv.neg_apply]
    exact ⟨fun hx => S.neg_mem x hx, fun hx => by simpa using S.neg_mem (-x) hx⟩
  · intro x hx
    simp only [Equiv.neg_apply, Rat.cast_neg, S.symm x hx]
    ring_nf

theorem phi_even (S : SpinLaw) (t : ℝ) : phi S (-t) = phi S t := by
  unfold phi
  change Real.log (mgf S (-t)) = Real.log (mgf S t)
  rw [mgf_even]



theorem hasDerivAt_mgf (S : SpinLaw) (t : ℝ) :
    HasDerivAt (mgf S) (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) t := by
  unfold mgf
  have hterm : ∀ x ∈ S.A,
      HasDerivAt (fun s : ℝ => (S.ρ x : ℝ) * Real.exp (s * (x : ℝ)))
        ((S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) t := by
    intro x _
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * (x : ℝ)))
        (Real.exp (t * (x : ℝ)) * (x : ℝ)) t :=
      ((hasDerivAt_id' t).mul_const (x : ℝ)).exp.congr_deriv (by ring)
    exact (hexp.const_mul (S.ρ x : ℝ)).congr_deriv (by ring)
  exact HasDerivAt.fun_sum fun x hx => hterm x hx

theorem hasDerivAt_phi (S : SpinLaw) (t : ℝ) :
    HasDerivAt (phi S)
      ((∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) / mgf S t) t := by
  change HasDerivAt (fun s => Real.log (mgf S s)) _ t
  exact (hasDerivAt_mgf S t).log (mgf_pos S t).ne'

theorem deriv_phi_eq (S : SpinLaw) (t : ℝ) :
    deriv (phi S) t = (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) / mgf S t :=
  (hasDerivAt_phi S t).deriv

theorem phi_contDiff (S : SpinLaw) : ContDiff ℝ ⊤ (phi S) := by
  have hmgf : ContDiff ℝ ⊤ (mgf S) := by
    unfold mgf
    refine ContDiff.sum fun x _ => contDiff_const.mul ((contDiff_id.mul contDiff_const).exp)
  change ContDiff ℝ ⊤ (fun t => Real.log (mgf S t))
  exact hmgf.log (fun t => (mgf_pos S t).ne')

theorem deriv_phi_neg (S : SpinLaw) (t : ℝ) : deriv (phi S) (-t) = -deriv (phi S) t := by
  have hdiff : Differentiable ℝ (phi S) := (phi_contDiff S).differentiable (by simp)
  have h1 : HasDerivAt (phi S) (deriv (phi S) (-t)) (-t) := (hdiff (-t)).hasDerivAt
  have hcomp : HasDerivAt (fun s => phi S (-s)) (-deriv (phi S) (-t)) t :=
    (h1.comp t (hasDerivAt_id' t).neg).congr_deriv (by ring)
  have hev : (fun s => phi S (-s)) = phi S := funext (phi_even S)
  rw [hev] at hcomp
  linarith [hcomp.deriv]

theorem deriv_phi_zero (S : SpinLaw) : deriv (phi S) 0 = 0 := by
  have h := deriv_phi_neg S 0
  simp only [neg_zero] at h
  linarith

theorem deriv_phi_bdd (S : SpinLaw) (t : ℝ) : |deriv (phi S) t| ≤ 1 := by
  rw [deriv_phi_eq, abs_div, abs_of_pos (mgf_pos S t), div_le_one (mgf_pos S t)]
  calc |∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))|
      ≤ ∑ x ∈ S.A, |(S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hρ : 0 ≤ (S.ρ x : ℝ) := by exact_mod_cast (S.pos x hx).le
        have hx1 : |(x : ℝ)| ≤ 1 := by
          have := S.mem_Icc x hx
          rw [abs_le]
          constructor
          · exact_mod_cast (by linarith : (-1 : ℚ) ≤ x)
          · exact_mod_cast (by linarith : x ≤ (1 : ℚ))
        rw [abs_mul, abs_mul, abs_of_nonneg hρ, abs_of_pos (Real.exp_pos _)]
        calc (S.ρ x : ℝ) * |(x : ℝ)| * Real.exp (t * (x : ℝ))
            ≤ (S.ρ x : ℝ) * 1 * Real.exp (t * (x : ℝ)) := by gcongr
          _ = (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by ring

theorem variance_pos (S : SpinLaw) : 0 < variance S := by
  unfold variance varQ
  have hmem : (1 : ℚ) ∈ S.A := S.one_mem
  have hnn : ∀ x ∈ S.A, 0 ≤ x ^ 2 * S.ρ x := fun x hx => mul_nonneg (sq_nonneg x) (S.pos x hx).le
  have hgt : (0 : ℚ) < ∑ x ∈ S.A, x ^ 2 * S.ρ x :=
    lt_of_lt_of_le (by have := S.pos 1 hmem; positivity) (Finset.single_le_sum hnn hmem)
  exact_mod_cast hgt

theorem tau_pos (S : SpinLaw) : 0 < tau S := by
  unfold tau tauQ
  have hv : 0 < varQ S := by
    have : 0 < (varQ S : ℝ) := variance_pos S
    exact_mod_cast this
  exact_mod_cast div_pos one_pos hv

theorem tau_mul_variance (S : SpinLaw) : tau S * variance S = 1 := by
  unfold tau tauQ variance
  have hv : (varQ S : ℝ) ≠ 0 := (variance_pos S).ne'
  push_cast; field_simp [hv]

theorem hasDerivAt_deriv_phi (S : SpinLaw) (t : ℝ) :
    HasDerivAt (deriv (phi S))
      (((∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) * mgf S t -
        (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) ^ 2) / (mgf S t) ^ 2) t := by
  let num : ℝ → ℝ := fun s => ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (s * (x : ℝ))
  have hnum : HasDerivAt num (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) t := by
    have hterm : ∀ x ∈ S.A,
        HasDerivAt (fun s : ℝ => (S.ρ x : ℝ) * (x : ℝ) * Real.exp (s * (x : ℝ)))
          ((S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) t := fun x _ => by
      have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * (x : ℝ)))
          (Real.exp (t * (x : ℝ)) * (x : ℝ)) t :=
        ((hasDerivAt_id' t).mul_const (x : ℝ)).exp.congr_deriv (by ring)
      exact (hexp.const_mul ((S.ρ x : ℝ) * (x : ℝ))).congr_deriv (by ring)
    exact HasDerivAt.fun_sum fun x hx => hterm x hx
  have hdiv := hnum.div (hasDerivAt_mgf S t) (mgf_pos S t).ne'
  refine (hdiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => deriv_phi_eq S s)).congr_deriv
    (by dsimp [num]; ring)

theorem deriv2_phi_nonneg (S : SpinLaw) (t : ℝ) : 0 ≤ iteratedDeriv 2 (phi S) t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, (hasDerivAt_deriv_phi S t).deriv]
  refine div_nonneg ?_ (sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S.A
    (fun x => Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))))
    (fun x => (x : ℝ) * Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))))
  have hL : (∑ x ∈ S.A, Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) *
      ((x : ℝ) * Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))))) ^ 2 =
      (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) ^ 2 := by
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have hnn : 0 ≤ (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
      have := (S.pos x hx).le; positivity
    calc Real.sqrt _ * ((x : ℝ) * Real.sqrt _) = (x : ℝ) * (Real.sqrt _ * Real.sqrt _) := by ring
      _ = (x : ℝ) * ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) := by rw [Real.mul_self_sqrt hnn]
      _ = _ := by ring
  have hR1 : ∑ x ∈ S.A, Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) ^ 2 = mgf S t := by
    unfold mgf
    refine Finset.sum_congr rfl fun x hx => Real.sq_sqrt (by have := (S.pos x hx).le; positivity)
  have hR2 : ∑ x ∈ S.A, ((x : ℝ) * Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ)))) ^ 2 =
      ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_pow, Real.sq_sqrt (by have := (S.pos x hx).le; positivity)]; ring
  rw [hL, hR1, hR2] at hcs; linarith

theorem iteratedDeriv2_phi_zero (S : SpinLaw) : iteratedDeriv 2 (phi S) 0 = variance S := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, (hasDerivAt_deriv_phi S 0).deriv, mgf_zero]
  have h1 : ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (0 * (x : ℝ)) = 0 := by
    have he := deriv_phi_zero S
    rw [deriv_phi_eq, mgf_zero, div_one] at he
    exact he
  rw [h1]
  simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), sub_zero, Real.exp_zero, mul_one, one_pow, div_one]
  unfold variance varQ
  push_cast
  refine Finset.sum_congr rfl fun x _ => by ring



theorem asOf_props_direct (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) :
    ∃ a : ℝ, 0 < a ∧ a = s * deriv (phi S) a ∧
      (∀ t : ℝ, 0 ≤ t → t < a → t / s < deriv (phi S) t ∨ t = 0) ∧
      (∀ t : ℝ, 0 ≤ t → a ≤ t → iteratedDeriv 2 (phi S) t ≤ 1 / s) ∧
      asOf S s = a := by
  have hτpos := tau_pos S
  have hs_pos : 0 < s := lt_trans hτpos hs
  have hvpos := variance_pos S
  have hτv := tau_mul_variance S
  let ψ : ℝ → ℝ := deriv (phi S)
  let ψ1 : ℝ → ℝ := iteratedDeriv 2 (phi S)
  have hψ_cont : Continuous ψ := by
    change Continuous (deriv (phi S))
    rw [← iteratedDeriv_one (f := phi S)]
    exact (phi_contDiff S).continuous_iteratedDeriv 1 (by simp)
  have hψ_diff : Differentiable ℝ ψ := by
    change Differentiable ℝ (deriv (phi S))
    rw [← iteratedDeriv_one (f := phi S)]
    exact (phi_contDiff S).differentiable_iteratedDeriv 1 (by simp)
  have hψ1_anti : AntitoneOn ψ1 (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      ((phi_contDiff S).continuous_iteratedDeriv 2 le_top).continuousOn
      (fun x _ => ((phi_contDiff S).differentiable_iteratedDeriv 2
        (by exact_mod_cast (WithTop.coe_lt_top (2 : ℕ∞) : ((2 : ℕ∞) : WithTop ℕ∞) < ⊤)) x).differentiableWithinAt)
      fun x hx => ?_
    have hd : HasDerivAt ψ1 (iteratedDeriv 3 (phi S) x) x := by
      rw [iteratedDeriv_succ]
      exact ((phi_contDiff S).differentiable_iteratedDeriv 2
        (by exact_mod_cast (WithTop.coe_lt_top (2 : ℕ∞) : ((2 : ℕ∞) : WithTop ℕ∞) < ⊤)) x).hasDerivAt
    rw [hd.deriv]
    exact hS x (interior_subset hx)
  let g : ℝ → ℝ := fun t => s * ψ t - t
  have hg_cont : Continuous g := (continuous_const.mul hψ_cont).sub continuous_id
  have hg_deriv : ∀ t, HasDerivAt g (s * ψ1 t - 1) t := fun t => by
    have hdψ : HasDerivAt ψ (ψ1 t) t := by
      rw [show ψ1 t = deriv ψ t by dsimp [ψ, ψ1]; rw [iteratedDeriv_succ, iteratedDeriv_one]]
      exact (hψ_diff t).hasDerivAt
    exact (hdψ.const_mul s).sub (hasDerivAt_id t)
  have hg'_0 : 0 < s * ψ1 0 - 1 := by
    have : ψ1 0 = variance S := iteratedDeriv2_phi_zero S
    rw [this]
    have h1 : 1 = tau S * variance S := hτv.symm
    nlinarith
  have hg_pos_small : ∃ a₀ : ℝ, 0 < a₀ ∧ 0 < g a₀ := by
    have hslope : Filter.Tendsto (slope g 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds (s * ψ1 0 - 1)) :=
      (hasDerivAt_iff_tendsto_slope.mp (hg_deriv 0)).mono_left
        (nhdsWithin_mono 0 fun _ hy => ne_of_gt hy)
    have hnhds : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), 0 < (g t - g 0) / (t - 0) := by
      filter_upwards [hslope.eventually (lt_mem_nhds hg'_0)] with t ht
      simpa [slope_def_field] using ht
    obtain ⟨U, hUpos, hU⟩ := Metric.mem_nhdsWithin_iff.mp hnhds
    have ha₀_pos : 0 < U / 2 := half_pos hUpos
    have hmemU : U / 2 ∈ Metric.ball (0 : ℝ) U ∩ Set.Ioi 0 :=
      ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha₀_pos]; exact half_lt_self hUpos,
        ha₀_pos⟩
    have ha₀_gt : 0 < (g (U / 2) - g 0) / (U / 2 - 0) := hU hmemU
    have hg0 : g 0 = 0 := by dsimp [g, ψ]; rw [deriv_phi_zero]; ring
    rw [hg0, sub_zero, sub_zero, div_pos_iff] at ha₀_gt
    rcases ha₀_gt with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact ⟨U / 2, ha₀_pos, h1⟩
    · linarith
  obtain ⟨a₀, ha₀_pos, ha₀_lt⟩ := hg_pos_small
  let a₁ : ℝ := max (a₀ + 1) (2 * s)
  have ha₁_gt : a₀ < a₁ := by linarith [le_max_left (a₀ + 1) (2 * s)]
  have hg_a₁ : g a₁ < 0 := by
    have hψ_le1 : ψ a₁ ≤ 1 := (abs_le.mp (deriv_phi_bdd S a₁)).2
    have h1 : s * ψ a₁ ≤ s := by nlinarith
    have h2 : 2 * s ≤ a₁ := le_max_right _ _
    dsimp [g]
    linarith
  have hIVT : ∃ a ∈ Set.Icc a₀ a₁, g a = 0 := by
    refine intermediate_value_Icc' ha₁_gt.le hg_cont.continuousOn ⟨hg_a₁.le, ha₀_lt.le⟩
  obtain ⟨a, ha_mem, ha_zero⟩ := hIVT
  have ha_pos : 0 < a := lt_of_lt_of_le ha₀_pos ha_mem.1
  have ha_eq : a = s * ψ a := by dsimp [g] at ha_zero; linarith
  have ha₀_lt_a : a₀ < a := by
    by_contra hle
    have heq : a = a₀ := le_antisymm (not_lt.mp hle) ha_mem.1
    rw [heq] at ha_zero
    linarith
  have hξ_neg : ∃ ξ ∈ Set.Ioo a₀ a, s * ψ1 ξ - 1 < 0 := by
    obtain ⟨ξ, hξmem, hξeq⟩ := exists_hasDerivAt_eq_slope g (fun t => s * ψ1 t - 1) ha₀_lt_a
      hg_cont.continuousOn (fun x _ => hg_deriv x)
    have hslope : (g a - g a₀) / (a - a₀) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr ha₀_lt_a)
    exact ⟨ξ, hξmem, by linarith⟩
  obtain ⟨ξ, hξmem, hg'ξ_neg⟩ := hξ_neg
  have hg'_neg_ge : ∀ t : ℝ, a ≤ t → s * ψ1 t - 1 < 0 := by
    intro t hta
    have hψ1_le : ψ1 t ≤ ψ1 ξ :=
      hψ1_anti (le_of_lt (lt_trans ha₀_pos hξmem.1)) (ha_pos.le.trans hta) (hξmem.2.le.trans hta)
    nlinarith
  have hψ1_le_inv : ∀ t : ℝ, 0 ≤ t → a ≤ t → ψ1 t ≤ 1 / s := by
    intro t _ hta
    have hlt := hg'_neg_ge t hta
    exact ((lt_div_iff₀' hs_pos).mpr (by linarith)).le
  have hg_pos_lt : ∀ t : ℝ, 0 < t → t < a → 0 < g t := by
    intro t ht0 hta
    by_contra! hle
    rcases le_or_gt t a₀ with hta₀ | ha₀t
    · have ht_lt_a₀ : t < a₀ := by
        rcases eq_or_lt_of_le hta₀ with rfl | hlt
        · linarith
        · exact hlt
      obtain ⟨c₁, hc₁mem, hc₁eq⟩ := exists_hasDerivAt_eq_slope g (fun x => s * ψ1 x - 1) ht0
        hg_cont.continuousOn (fun x _ => hg_deriv x)
      obtain ⟨c₂, hc₂mem, hc₂eq⟩ := exists_hasDerivAt_eq_slope g (fun x => s * ψ1 x - 1) ht_lt_a₀
        hg_cont.continuousOn (fun x _ => hg_deriv x)
      have hg0 : g 0 = 0 := by dsimp [g, ψ]; rw [deriv_phi_zero]; ring
      have hc₁_le : s * ψ1 c₁ - 1 ≤ 0 := by
        have hdiv : (g t - g 0) / (t - 0) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr ht0).le
        linarith
      have hc₂_gt : 0 < s * ψ1 c₂ - 1 := by
        have hdiv : 0 < (g a₀ - g t) / (a₀ - t) :=
          div_pos (by linarith) (sub_pos.mpr ht_lt_a₀)
        linarith
      have hc_anti : ψ1 c₂ ≤ ψ1 c₁ :=
        hψ1_anti hc₁mem.1.le (hc₂mem.1.trans' ht0).le (hc₁mem.2.le.trans hc₂mem.1.le)
      nlinarith
    · obtain ⟨c₁, hc₁mem, hc₁eq⟩ := exists_hasDerivAt_eq_slope g (fun x => s * ψ1 x - 1) ha₀t
        hg_cont.continuousOn (fun x _ => hg_deriv x)
      obtain ⟨c₂, hc₂mem, hc₂eq⟩ := exists_hasDerivAt_eq_slope g (fun x => s * ψ1 x - 1) hta
        hg_cont.continuousOn (fun x _ => hg_deriv x)
      have hc₁_lt : s * ψ1 c₁ - 1 < 0 := by
        have hdiv : (g t - g a₀) / (t - a₀) < 0 :=
          div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr ha₀t)
        linarith
      have hc₂_ge : 0 ≤ s * ψ1 c₂ - 1 := by
        have hdiv : 0 ≤ (g a - g t) / (a - t) :=
          div_nonneg (by linarith) (sub_pos.mpr hta).le
        linarith
      have hc_anti : ψ1 c₂ ≤ ψ1 c₁ :=
        hψ1_anti (ha₀_pos.le.trans hc₁mem.1.le) (ht0.le.trans hc₂mem.1.le)
          (hc₁mem.2.le.trans hc₂mem.1.le)
      nlinarith
  have hlt_cond : ∀ t : ℝ, 0 ≤ t → t < a → t / s < ψ t ∨ t = 0 := by
    intro t ht0 hta
    rcases eq_or_lt_of_le ht0 with rfl | htpos
    · exact Or.inr rfl
    · refine Or.inl ?_
      rw [div_lt_iff₀ hs_pos]
      have hgt := hg_pos_lt t htpos hta
      dsimp [g] at hgt
      linarith
  have hasOf_set : {b : ℝ | 0 < b ∧ b = s * ψ b} = {a} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨?_, fun hb => by subst hb; exact ⟨ha_pos, ha_eq⟩⟩
    rintro ⟨hb_pos, hb_eq⟩
    have hgb : g b = 0 := by dsimp [g]; linarith
    rcases lt_trichotomy b a with hba | rfl | hab
    · linarith [hg_pos_lt b hb_pos hba]
    · rfl
    · obtain ⟨c, hcmem, hceq⟩ := exists_hasDerivAt_eq_slope g (fun x => s * ψ1 x - 1) hab
        hg_cont.continuousOn (fun x _ => hg_deriv x)
      have hneg := hg'_neg_ge c hcmem.1.le
      have hzero : (g b - g a) / (b - a) = 0 := by rw [hgb, ha_zero, sub_self, zero_div]
      linarith
  have hasOf_eq : asOf S s = a := by
    unfold asOf
    change sSup {b : ℝ | 0 < b ∧ b = s * ψ b} = a
    rw [hasOf_set, csSup_singleton]
  exact ⟨a, ha_pos, ha_eq, hlt_cond, hψ1_le_inv, hasOf_eq⟩

theorem fs_even (S : SpinLaw) (s t : ℝ) : fs S s (-t) = fs S s t := by
  unfold fs; rw [neg_sq, phi_even]

theorem hasDerivAt_fs (S : SpinLaw) {s : ℝ} (hs_pos : 0 < s) (t : ℝ) :
    HasDerivAt (fs S s) (t / s - deriv (phi S) t) t := by
  unfold fs
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * s)) (t / s) t := by
    have hsq := ((hasDerivAt_id' t).pow 2).div_const (2 * s)
    rw [show (↑(2 : ℕ) * t ^ (2 - 1) * 1) / (2 * s) = t / s by
      calc ((↑(2 : ℕ) : ℝ) * t ^ (2 - 1) * 1) / (2 * s) = (2 * t) / (2 * s) := by norm_num
        _ = t / s := mul_div_mul_left t s (by norm_num)] at hsq
    exact hsq
  have h2 : HasDerivAt (phi S) (deriv (phi S) t) t := by
    rw [deriv_phi_eq S t]
    exact hasDerivAt_phi S t
  exact h1.sub h2

theorem gs_eq_fs_max (S : SpinLaw) (s t : ℝ) :
    gs S s t = fs S s (max (asOf S s) |t|) := by
  unfold gs
  split_ifs with h
  · rw [max_eq_left h]
  · rw [max_eq_right (lt_of_not_ge h).le]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht, fs_even]

theorem gs_continuous (S : SpinLaw) (s : ℝ) : Continuous (gs S s) := by
  have hfs_cont : Continuous (fs S s) :=
    ((continuous_pow 2).div_const _).sub (phi_contDiff S).continuous
  have heq : gs S s = fun t => fs S s (max (asOf S s) |t|) := funext (gs_eq_fs_max S s)
  rw [heq]
  exact hfs_cont.comp (continuous_const.max continuous_abs)

theorem phis_continuous (S : SpinLaw) (s : ℝ) : Continuous (phis S s) := by
  change Continuous (fun t => t ^ 2 / (2 * s) - gs S s t)
  exact ((continuous_pow 2).div_const _).sub (gs_continuous S s)

theorem ds_continuous (S : SpinLaw) (s : ℝ) : Continuous (ds S s) := by
  change Continuous (fun t => fs S s t - gs S s t)
  have hfs_cont : Continuous (fs S s) :=
    ((continuous_pow 2).div_const _).sub (phi_contDiff S).continuous
  exact hfs_cont.sub (gs_continuous S s)

theorem gs_even (S : SpinLaw) (s t : ℝ) : gs S s (-t) = gs S s t := by
  simp only [gs_eq_fs_max, abs_neg]

theorem ds_even (S : SpinLaw) (s t : ℝ) : ds S s (-t) = ds S s t := by
  unfold ds; rw [fs_even, gs_even]

theorem phis_even (S : SpinLaw) (s t : ℝ) : phis S s (-t) = phis S s t := by
  unfold phis; rw [neg_sq, gs_even]

theorem hasDerivAt_gs_direct (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) (t : ℝ) :
    HasDerivAt (gs S s) (if |t| ≤ asOf S s then 0 else t / s - deriv (phi S) t) t := by
  obtain ⟨a, ha_pos, ha_eq, _, _, hasOf⟩ := asOf_props_direct S hS hs
  rw [hasOf]
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  rcases lt_trichotomy |t| a with hlt | heq | hgt
  · rw [if_pos hlt.le]
    have hev : gs S s =ᶠ[nhds t] fun _ => fs S s a := by
      have hopen : IsOpen (Set.Ioo (-a) a) := isOpen_Ioo
      have hmem : t ∈ Set.Ioo (-a) a := abs_lt.mp hlt
      filter_upwards [hopen.mem_nhds hmem] with y hy
      unfold gs
      rw [hasOf, if_pos (abs_lt.mpr hy).le]
    exact (hasDerivAt_const t (fs S s a)).congr_of_eventuallyEq hev
  · rw [if_pos heq.le]
    have hpos_a : HasDerivAt (gs S s) 0 a := by
      have hleft : HasDerivWithinAt (gs S s) 0 (Set.Icc 0 a) a := by
        refine (hasDerivAt_const a (fs S s a)).hasDerivWithinAt.congr_of_mem ?_
          ⟨ha_pos.le, le_rfl⟩
        intro y hy
        unfold gs
        rw [hasOf, if_pos (by rw [abs_of_nonneg hy.1]; exact hy.2)]
      have hright : HasDerivWithinAt (gs S s) 0 (Set.Ici a) a := by
        have hfa : HasDerivAt (fs S s) 0 a := by
          have h0 : a / s = deriv (phi S) a := div_eq_of_eq_mul hs_pos.ne' (ha_eq.trans (mul_comm _ _))
          exact (hasDerivAt_fs S hs_pos a).congr_deriv (by rw [h0, sub_self])
        refine hfa.hasDerivWithinAt.congr_of_mem ?_ Set.self_mem_Ici
        intro y hy
        have hya : a ≤ y := hy
        have hypos : 0 ≤ y := ha_pos.le.trans hya
        unfold gs
        rw [hasOf]
        split_ifs with hle
        · have : y = a := le_antisymm (by rwa [abs_of_nonneg hypos] at hle) hya
          subst this; rfl
        · rfl
      have hunion := hleft.union hright
      have hsub : Set.Ici 0 ⊆ Set.Icc 0 a ∪ Set.Ici a := fun y hy => by
        rcases le_or_gt y a with h | h
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr h.le
      exact (hunion.mono hsub).hasDerivAt (Ici_mem_nhds ha_pos)
    rcases abs_eq ha_pos.le |>.mp heq with rfl | rfl
    · exact hpos_a
    · have hpos_neg : HasDerivAt (gs S s) 0 (-(-a)) := by simpa using hpos_a
      have hcomp : HasDerivAt (fun x => gs S s (-x)) 0 (-a) :=
        (hpos_neg.comp (-a) ((hasDerivAt_id' (-a)).neg)).congr_deriv (by ring)
      have hev_neg : (fun x => gs S s (-x)) = gs S s := funext (gs_even S s)
      rw [hev_neg] at hcomp
      exact hcomp
  · rw [if_neg (not_le_of_gt hgt)]
    have hev : gs S s =ᶠ[nhds t] fs S s := by
      have hopen : IsOpen {y : ℝ | a < |y|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
      filter_upwards [hopen.mem_nhds hgt] with y hy
      unfold gs
      rw [hasOf, if_neg (not_le_of_gt hy)]
    exact (hasDerivAt_fs S hs_pos t).congr_of_eventuallyEq hev

theorem hasDerivAt_phis_direct (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t : ℝ) :
    HasDerivAt (phis S s) (if |t| ≤ asOf S s then t / s else deriv (phi S) t) t := by
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * s)) (t / s) t := by
    have hsq := ((hasDerivAt_id' t).pow 2).div_const (2 * s)
    rw [show (↑(2 : ℕ) * t ^ (2 - 1) * 1) / (2 * s) = t / s by
      calc ((↑(2 : ℕ) : ℝ) * t ^ (2 - 1) * 1) / (2 * s) = (2 * t) / (2 * s) := by norm_num
        _ = t / s := mul_div_mul_left t s (by norm_num)] at hsq
    exact hsq
  have h2 := h1.sub (hasDerivAt_gs_direct S hS hs t)
  change HasDerivAt (phis S s) _ t
  exact h2.congr_deriv (by split_ifs <;> ring)





theorem hasDerivAt_ds_direct (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t : ℝ) :
    HasDerivAt (ds S s) (if |t| ≤ asOf S s then t / s - deriv (phi S) t else 0) t := by
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  have h := (hasDerivAt_fs S hs_pos t).sub (hasDerivAt_gs_direct S hS hs t)
  change HasDerivAt (ds S s) _ t
  exact h.congr_deriv (by split_ifs <;> ring)

theorem abs_deriv_ds_le_one (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t : ℝ) : |deriv (ds S s) t| ≤ 1 := by
  rw [(hasDerivAt_ds_direct S hS hs t).deriv]
  obtain ⟨a, ha_pos, ha_eq, hlt_cond, _, hasOf⟩ := asOf_props_direct S hS hs
  rw [hasOf]
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  split_ifs with hle
  · have h_nonneg_case : ∀ u : ℝ, 0 ≤ u → u ≤ a → |u / s - deriv (phi S) u| ≤ 1 := by
      intro u hu0 hua
      rcases eq_or_lt_of_le hua with rfl | hlt
      · have h0 : u / s = deriv (phi S) u := div_eq_of_eq_mul hs_pos.ne' (ha_eq.trans (mul_comm _ _))
        rw [h0, sub_self, abs_zero]; exact zero_le_one
      · have hψ1 : deriv (phi S) u ≤ 1 := (abs_le.mp (deriv_phi_bdd S u)).2
        rcases hlt_cond u hu0 hlt with hdiv | rfl
        · have hu_s_nn : 0 ≤ u / s := div_nonneg hu0 hs_pos.le
          rw [abs_of_nonpos (by linarith)]
          linarith
        · simp [deriv_phi_zero]
    rcases le_or_gt 0 t with ht0 | ht0
    · exact h_nonneg_case t ht0 (by rwa [abs_of_nonneg ht0] at hle)
    · have hneg : |(-t) / s - deriv (phi S) (-t)| ≤ 1 :=
        h_nonneg_case (-t) (by linarith) (by rwa [abs_of_neg ht0] at hle)
      rw [deriv_phi_neg] at hneg
      have heq_neg : (-t) / s - -deriv (phi S) t = -(t / s - deriv (phi S) t) := by
        rw [neg_div]; ring
      rwa [heq_neg, abs_neg] at hneg
  · norm_num

theorem ds_sub_le (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t₁ t₂ : ℝ) : |ds S s t₁ - ds S s t₂| ≤ |t₁ - t₂| := by
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := ds S s) (C := 1)
    (fun x _ => (hasDerivAt_ds_direct S hS hs x).differentiableAt)
    (fun x _ => by simpa [Real.norm_eq_abs] using abs_deriv_ds_le_one S hS hs x)
    (Set.mem_univ t₂) (Set.mem_univ t₁)
  simpa [Real.norm_eq_abs, one_mul] using h

theorem ds_nonneg (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) (t : ℝ) :
    0 ≤ ds S s t := by
  obtain ⟨a, ha_pos, ha_eq, hlt_cond, _, hasOf⟩ := asOf_props_direct S hS hs
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  unfold ds gs
  split_ifs with hle
  · have hfs_anti : AntitoneOn (fs S s) (Set.Icc 0 a) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 a) ?_ ?_ fun x hx => ?_
      · exact (((continuous_pow 2).div_const _).sub (phi_contDiff S).continuous).continuousOn
      · exact fun x _ => (hasDerivAt_fs S hs_pos x).differentiableAt.differentiableWithinAt
      · rw [(hasDerivAt_fs S hs_pos x).deriv]
        have hx' := interior_subset hx
        rcases eq_or_lt_of_le hx'.2 with rfl | hlt
        · have h0 : x / s = deriv (phi S) x := div_eq_of_eq_mul hs_pos.ne' (ha_eq.trans (mul_comm _ _))
          linarith
        · rcases hlt_cond x hx'.1 hlt with hdiv | rfl
          · linarith
          · simp [deriv_phi_zero]
    have hstep := hfs_anti ⟨abs_nonneg t, by rwa [hasOf] at hle⟩ ⟨ha_pos.le, le_rfl⟩
      (by rwa [hasOf] at hle)
    have hfs_abs : fs S s |t| = fs S s t := by
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht]
      · rw [abs_of_neg ht, fs_even]
    rw [hfs_abs] at hstep
    rw [hasOf]
    linarith
  · linarith

theorem deriv_phis_mono_and_lip (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    {t₁ t₂ : ℝ} (hle : t₁ ≤ t₂) :
    0 ≤ deriv (phis S s) t₂ - deriv (phis S s) t₁ ∧
      deriv (phis S s) t₂ - deriv (phis S s) t₁ ≤ (1 / s) * (t₂ - t₁) := by
  obtain ⟨a, ha_pos, ha_eq, _, hψ1_le, hasOf⟩ := asOf_props_direct S hS hs
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  let q := deriv (phis S s)
  have hq_eq : ∀ t, q t = if |t| ≤ a then t / s else deriv (phi S) t := fun t => by
    dsimp [q]; rw [(hasDerivAt_phis_direct S hS hs t).deriv, hasOf]
  have hq_ge_a : ∀ t, a ≤ t → q t = deriv (phi S) t := fun t ht => by
    rw [hq_eq]
    split_ifs with h
    · have : t = a := le_antisymm (by rwa [abs_of_nonneg (ha_pos.le.trans ht)] at h) ht
      subst this
      exact div_eq_of_eq_mul hs_pos.ne' (ha_eq.trans (mul_comm _ _))
    · rfl
  have hq_Icc : ∀ t, |t| ≤ a → q t = t / s := fun t ht => by rw [hq_eq, if_pos ht]
  have hq_le_neg_a : ∀ t, t ≤ -a → q t = deriv (phi S) t := fun t ht => by
    rw [hq_eq]
    split_ifs with h
    · have : t = -a := le_antisymm ht (by
        have h1 := (abs_le.mp h).1
        linarith)
      subst this
      have h0 : a / s = deriv (phi S) a := div_eq_of_eq_mul hs_pos.ne' (ha_eq.trans (mul_comm _ _))
      rw [deriv_phi_neg, neg_div, h0]
    · rfl
  have h_on_Ici : ∀ x y, a ≤ x → x ≤ y → 0 ≤ q y - q x ∧ q y - q x ≤ (1 / s) * (y - x) := by
    intro x y hax hxy
    rw [hq_ge_a x hax, hq_ge_a y (hax.trans hxy)]
    have hderiv_cont : Continuous (deriv (phi S)) := by
      rw [← iteratedDeriv_one (f := phi S)]
      exact (phi_contDiff S).continuous_iteratedDeriv 1 (by simp)
    have hderiv_diff : Differentiable ℝ (deriv (phi S)) := by
      rw [← iteratedDeriv_one (f := phi S)]
      exact (phi_contDiff S).differentiable_iteratedDeriv 1 (by simp)
    have hmono : MonotoneOn (deriv (phi S)) (Set.Ici a) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici a)
        hderiv_cont.continuousOn
        (fun z _ => (hderiv_diff z).differentiableWithinAt)
        fun z _ => ?_
      rw [← iteratedDeriv_one (f := phi S), ← iteratedDeriv_succ]
      exact deriv2_phi_nonneg S z
    have hdiff_nn := sub_nonneg.mpr (hmono hax (hax.trans hxy) hxy)
    have hlip := (convex_Ici a).norm_image_sub_le_of_norm_deriv_le (f := deriv (phi S)) (C := 1 / s)
      (fun z _ => hderiv_diff z)
      (fun z hz => by
        have hd : deriv (deriv (phi S)) z = iteratedDeriv 2 (phi S) z := by
          rw [iteratedDeriv_succ, iteratedDeriv_one]
        rw [hd, Real.norm_eq_abs, abs_of_nonneg (deriv2_phi_nonneg S z)]
        exact hψ1_le z (ha_pos.le.trans hz.out) hz.out)
      hax (hax.trans hxy)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hdiff_nn,
      abs_of_nonneg (sub_nonneg.mpr hxy)] at hlip
    exact ⟨hdiff_nn, hlip⟩
  have h_on_Icc : ∀ x y, -a ≤ x → x ≤ y → y ≤ a →
      0 ≤ q y - q x ∧ q y - q x ≤ (1 / s) * (y - x) := by
    intro x y hxa hxy hya
    rw [hq_Icc x (abs_le.mpr ⟨hxa, hxy.trans hya⟩), hq_Icc y (abs_le.mpr ⟨hxa.trans hxy, hya⟩)]
    have h1 : y / s - x / s = (1 / s) * (y - x) := by ring
    rw [h1]
    exact ⟨mul_nonneg (div_nonneg zero_le_one hs_pos.le) (sub_nonneg.mpr hxy), le_rfl⟩
  have h_on_Iic : ∀ x y, x ≤ y → y ≤ -a → 0 ≤ q y - q x ∧ q y - q x ≤ (1 / s) * (y - x) := by
    intro x y hxy hya
    rw [hq_le_neg_a x (hxy.trans hya), hq_le_neg_a y hya]
    have hstep := h_on_Ici (-y) (-x) (by linarith) (by linarith)
    rw [hq_ge_a (-y) (by linarith), hq_ge_a (-x) (by linarith),
      deriv_phi_neg, deriv_phi_neg] at hstep
    convert hstep using 2 <;> ring
  rcases le_or_gt t₁ (-a) with ht₁_neg | ht₁_gt_neg
  · rcases le_or_gt t₂ (-a) with ht₂_neg | ht₂_gt_neg
    · exact h_on_Iic t₁ t₂ hle ht₂_neg
    · rcases le_or_gt t₂ a with ht₂_le_a | ht₂_gt_a
      · have h1 := h_on_Iic t₁ (-a) ht₁_neg le_rfl
        have h2 := h_on_Icc (-a) t₂ le_rfl ht₂_gt_neg.le ht₂_le_a
        exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
      · have h1 := h_on_Iic t₁ (-a) ht₁_neg le_rfl
        have h2 := h_on_Icc (-a) a le_rfl (by linarith [ha_pos]) le_rfl
        have h3 := h_on_Ici a t₂ le_rfl ht₂_gt_a.le
        exact ⟨by linarith [h1.1, h2.1, h3.1], by linarith [h1.2, h2.2, h3.2]⟩
  · rcases le_or_gt t₁ a with ht₁_le_a | ht₁_gt_a
    · rcases le_or_gt t₂ a with ht₂_le_a | ht₂_gt_a
      · exact h_on_Icc t₁ t₂ ht₁_gt_neg.le hle ht₂_le_a
      · have h1 := h_on_Icc t₁ a ht₁_gt_neg.le ht₁_le_a le_rfl
        have h2 := h_on_Ici a t₂ le_rfl ht₂_gt_a.le
        exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
    · exact h_on_Ici t₁ t₂ ht₁_gt_a.le hle



end SpinAndPhi

section LinearAlgebraAndHessian



























end LinearAlgebraAndHessian

end CritWinSpin.Implementation.EnvelopeAnalysis

end

section

set_option autoImplicit false
open scoped RealInnerProductSpace
noncomputable section

namespace CritWinSpin.Implementation.SmoothGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]









end CritWinSpin.Implementation.SmoothGeometry

end

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeGeometry

open EnvelopeAnalysis













theorem normSq_coe {N : ℕ} (z : Point N) : normSq (fun i => z i) = ‖z‖ ^ 2 := by
  exact (EuclideanSpace.real_norm_sq_eq z).symm











theorem continuous_potential {N : ℕ} (S : SpinLaw) (s a : ℝ)
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) :
    Continuous (potential S s a L h) := by
  have hphi := phis_continuous S s
  unfold potential Ualpha Wpot normSq Matrix.mulVec dotProduct
  fun_prop

end CritWinSpin.Implementation.EnvelopeGeometry

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.PiVolumeTransfer

open DensityAnalysis

theorem integrable_iff {N : ℕ} (f : (Fin N → ℝ) → ℝ) :
    Integrable (fun z : Point N => f (fun i => z i)) ↔ Integrable f := by
  let e := MeasurableEquiv.toLp 2 (Fin N → ℝ)
  have h := (PiLp.volume_preserving_toLp (Fin N)).integrable_comp_emb
    e.measurableEmbedding (g := fun z : Point N => f (fun i => z i))
  simpa only [Function.comp_def, WithLp.ofLp_toLp] using h.symm

theorem integral_eq {N : ℕ} (f : (Fin N → ℝ) → ℝ) :
    (∫ z : Point N, f (fun i => z i)) = ∫ z : Fin N → ℝ, f z := by
  let e := MeasurableEquiv.toLp 2 (Fin N → ℝ)
  have h := (PiLp.volume_preserving_toLp (Fin N)).integral_comp
    e.measurableEmbedding (fun z : Point N => f (fun i => z i))
  simpa only [Function.comp_def, WithLp.ofLp_toLp] using h.symm

theorem gibbs_integral_eq {N : ℕ} (U f : (Fin N → ℝ) → ℝ)
    (hU : Continuous (fun z : Point N => U (fun i => z i)))
    (hiU : Integrable (fun z : Fin N → ℝ => Real.exp (-U z))) :
    (∫ z : Point N, f (fun i => z i) ∂DensityAnalysis.gibbs (fun z => U (fun i => z i))) =
      ∫ z : Fin N → ℝ, f z * normDens U z := by
  have hiU' := (integrable_iff (fun z => Real.exp (-U z))).2 hiU
  rw [integral_gibbs hU hiU']
  rw [integral_eq (fun z => Real.exp (-U z) * f z), integral_eq (fun z => Real.exp (-U z))]
  have he : (fun z : Fin N → ℝ => f z * normDens U z) =
      fun z => (Real.exp (-U z) * f z) / (∫ y, Real.exp (-U y)) := by
    funext z
    unfold normDens
    ring
  rw [he, integral_div]

end CritWinSpin.Implementation.PiVolumeTransfer

end

end

section

set_option autoImplicit false
open MeasureTheory

namespace CritWinSpin.Implementation.Regularization











variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f R : Ω → ℝ)











end CritWinSpin.Implementation.Regularization

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.RegularizedGibbsMoments

open DensityAnalysis







end CritWinSpin.Implementation.RegularizedGibbsMoments

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeMoments

open DensityAnalysis EnvelopeGeometry



end CritWinSpin.Implementation.EnvelopeMoments

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open CritWinSpin
open scoped NNReal

namespace CritWinSpin.Implementation.EnvelopeCertificate
open DensityAnalysis LangevinBudget EnvelopeGeometry



end CritWinSpin.Implementation.EnvelopeCertificate
end

end

section
set_option autoImplicit false
noncomputable section

namespace CritWinSpin.Implementation.MomentBudget

theorem bounds {B M D E : ℝ} (hB : 131072 ≤ B) (hM : M ≤ B)
    (hD0 : 0 ≤ D) (hD : D ≤ B) (hE : E ≤ B ^ 4) :
    B ≤ B ^ 100 ∧ 2 ≤ B ^ 100 ∧
    0 < 1 / B ∧ 1 / B ≤ 1 ∧ (1 / B) * M ≤ 1 ∧
    1 ≤ (1 / B) * B ^ 100 ∧
    1 + (32 / (1 / B) ^ 2) * M ≤ B ^ 100 ∧
    2 + (65536 / (1 / B) ^ 2) * M + 32 * D ^ 3 + E ≤ B ^ 100 := by
  have hBp : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hB3 : 1 ≤ B ^ 3 := one_le_pow₀ hB1
  have hB4 : 2 ≤ B ^ 4 := by
    have hh := mul_le_mul_of_nonneg_left hB3 hBp.le
    nlinarith only [hh, hB]
  have hBR : B ≤ B ^ 100 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB1 (show 1 ≤ (100 : ℕ) by decide)
  have hB5R : B ^ 5 ≤ B ^ 100 := pow_le_pow_right₀ hB1 (by decide)
  have hNorm : 1 + 32 * B ^ 3 ≤ B ^ 5 := by
    have hCoeff : (33 : ℝ) ≤ B ^ 2 := by nlinarith only [hB]
    have hh := mul_le_mul_of_nonneg_right hCoeff (pow_nonneg hBp.le 3)
    nlinarith only [hh, hB3]
  have hGrad : 2 + 65536 * B ^ 3 + 32 * B ^ 3 + B ^ 4 ≤ B ^ 5 := by
    have hc : 65568 * B ^ 3 ≤ B ^ 4 := by
      have hh := mul_le_mul_of_nonneg_right (show (65568 : ℝ) ≤ B by linarith only [hB])
        (pow_nonneg hBp.le 3)
      nlinarith only [hh]
    have h5 : 3 * B ^ 4 ≤ B ^ 5 := by
      have hh := mul_le_mul_of_nonneg_right (show (3 : ℝ) ≤ B by linarith only [hB])
        (pow_nonneg hBp.le 4)
      nlinarith only [hh]
    nlinarith only [hc, h5, hB4]
  have hMul : (1 / B) * B = 1 := by field_simp [hBp.ne']
  have haM : (1 / B) * M ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hM (show 0 ≤ 1 / B by positivity)
    rwa [hMul] at hh
  have haR : 1 ≤ (1 / B) * B ^ 100 := by
    have hh := mul_le_mul_of_nonneg_left hBR (show 0 ≤ 1 / B by positivity)
    rwa [hMul] at hh
  have hMS : (1 / (1 / B) ^ 2) * M ≤ B ^ 3 := by
    have he : (1 / (1 / B) ^ 2) * M = B ^ 2 * M := by field_simp [hBp.ne']
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hM (sq_nonneg B)
    nlinarith only [hh]
  have hD3 := pow_le_pow_left₀ hD0 hD 3
  refine ⟨hBR, (by linarith only [hBR, hB]), by positivity,
    (div_le_one hBp).2 hB1, haM, haR, ?_, ?_⟩
  · apply le_trans ?_ (hNorm.trans hB5R)
    have hh := mul_le_mul_of_nonneg_left hMS (show (0:ℝ) ≤ 32 by norm_num)
    have he : (32 / (1 / B) ^ 2) * M = 32 * ((1 / (1 / B) ^ 2) * M) := by ring
    rw [he]
    linarith only [hh]
  · apply le_trans ?_ (hGrad.trans hB5R)
    have hh := mul_le_mul_of_nonneg_left hMS (show (0:ℝ) ≤ 65536 by norm_num)
    have he : (65536 / (1 / B) ^ 2) * M = 65536 * ((1 / (1 / B) ^ 2) * M) := by ring
    rw [he]
    nlinarith only [hh, hD3, hE]

end CritWinSpin.Implementation.MomentBudget
end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeParameters
open DensityAnalysis EnvelopeGeometry LangevinBudget

def baseBudget (C : ℝ) (N : ℕ) (t : ℝ) : ℝ := C * ((N : ℝ) + 1) * (t + 1)

theorem setup {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s C M₀ Cₖ t : ℝ}
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hs : tau S < s) (hsC : s ≤ C) (ht : 0 ≤ t)
    (hC : 131072 ≤ C) (hM₀ : 0 ≤ M₀) (hMC : 2048 * M₀ ≤ C)
    (hCₖ : 0 ≤ Cₖ) (hKC : 2 * Cₖ ≤ C) (hGC : GaussianMoments.sixthConstant ≤ C)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (hiW : Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z)))
    (hiW2 : Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Wpot S s L h z)))
    (hiU : Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S s (1 / baseBudget C N t) L h z)))
    (hMom : (∫ z : Fin N → ℝ, normSq z * normDens (Wpot S s L h) z) ≤ M₀ * (N : ℝ)) :
    let B := baseBudget C N t
    ∃ cert : Certificate N (1 / B),
      cert.U = potential S s (1 / B) L h ∧ cert.g = gradient S s (1 / B) L h ∧
      0 < 1 / B ∧ 1 / B ≤ 1 ∧ 2 ≤ B ^ 100 ∧ 1 ≤ (1 / B) * B ^ 100 ∧
      (∫ x, ‖x‖ ∂DensityAnalysis.gibbs cert.U) ≤ B ^ 100 ∧
      2 + (∫ x, ‖cert.g x‖ ^ 6 ∂DensityAnalysis.gibbs cert.U) +
        GaussianMoments.sixthConstant * (N : ℝ) ^ 3 ≤ B ^ 100 ∧
      2 * (Cₖ * Real.sqrt (N : ℝ)) ≤ B ^ 100 ∧
      1 / (4 * B ^ 100) + (1 / B) * M₀ * (N : ℝ) / 2 ≤ 1 / (2048 * (t + 1)) := by
  simpa only [EnvelopeParameters.baseBudget] using
    (CritWinSpin.regularized_envelope_budget S hS L h hs hsC ht hC hM₀ hMC hCₖ hKC hGC hPSD
      hiW hiW2 hiU hMom)

end CritWinSpin.Implementation.EnvelopeParameters
end

end



section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2
open Turing StateTransition QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary













end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC

def wordValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (wordValue bs)

theorem wordValue_bits (n : ℕ) : wordValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp [wordValue, ih]

def readQuoted : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bs, tail) ← readQuoted rest
      pure (b :: bs, tail)
  | _ => none

theorem readQuoted_encode (bs tail : List Bool) :
    readQuoted (bs.flatMap (fun b => [true, b]) ++ false :: false :: tail) =
      some (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [readQuoted, ih]

def readBin (xs : List Bool) : Option (ℕ × List Bool) := do
  let (bs, rest) ← readQuoted xs
  pure (wordValue bs, rest)

theorem readBin_encBin (n : ℕ) (tail : List Bool) :
    readBin (encBin n ++ tail) = some (n, tail) := by
  simp [readBin, encBin, List.append_assoc, readQuoted_encode, wordValue_bits]

def readInt : List Bool → Option (ℤ × List Bool)
  | sign :: xs => do
      let (n, tail) ← readBin xs
      pure ((if sign then -(n : ℤ) else (n : ℤ)), tail)
  | [] => none

theorem readInt_encInt (z : ℤ) (tail : List Bool) :
    readInt (encInt z ++ tail) = some (z, tail) := by
  by_cases hz : z < 0
  · simp [encInt, hz, readInt, readBin_encBin, abs_of_neg hz]
  · simp [encInt, hz, readInt, readBin_encBin, abs_of_nonneg (le_of_not_gt hz)]

def readRat (xs : List Bool) : Option (ℚ × List Bool) := do
  let (num, rest) ← readInt xs
  let (den, tail) ← readBin rest
  pure (Rat.divInt num den, tail)

theorem readRat_encRat (q : ℚ) (tail : List Bool) :
    readRat (encRat q ++ tail) = some (q, tail) := by
  simp [readRat, encRat, List.append_assoc, readInt_encInt, readBin_encBin]

def readRats : ℕ → List Bool → Option (List ℚ × List Bool)
  | 0, xs => some ([], xs)
  | n + 1, xs => do
      let (q, rest) ← readRat xs
      let (qs, tail) ← readRats n rest
      pure (q :: qs, tail)

theorem readRats_encode (qs : List ℚ) (tail : List Bool) :
    readRats qs.length (qs.flatMap encRat ++ tail) = some (qs, tail) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [readRats, List.append_assoc, readRat_encRat, ih]













theorem ofFn_flatMap {α β : Type} {N : ℕ} (f : Fin N → α) (g : α → List β) :
    (List.ofFn f).flatMap g = (List.ofFn (fun i => g (f i))).flatten := by
  induction N with
  | zero => rfl
  | succ N ih => simp [List.ofFn_succ, ih]

theorem readRats_encConfig {S : SpinLaw} {N : ℕ} (x : Config S (Fin N)) (tail : List Bool) :
    readRats N (encConfig x ++ tail) = some (List.ofFn (fun i => (x i : ℚ)), tail) := by
  have h := readRats_encode (List.ofFn (fun i => (x i : ℚ))) tail
  simpa only [List.length_ofFn, ofFn_flatMap, encConfig] using h

theorem encConfig_injective {S : SpinLaw} {N : ℕ} :
    Function.Injective (encConfig (S := S) (N := N)) := by
  intro x y hxy
  have h := readRats_encConfig x []
  rw [hxy, readRats_encConfig y []] at h
  have hlists : List.ofFn (fun i => (y i : ℚ)) = List.ofFn (fun i => (x i : ℚ)) :=
    congrArg Prod.fst (Option.some.inj h)
  have hfun := List.ofFn_injective hlists
  funext i
  apply Subtype.ext
  exact (congrFun hfun i).symm

theorem decConfig_encConfig {S : SpinLaw} {N : ℕ} (x : Config S (Fin N)) :
    decConfig S N (encConfig x) = some x := by
  classical
  unfold decConfig
  split_ifs with h
  · congr 1
    exact encConfig_injective (Classical.choose_spec h)
  · exact False.elim (h ⟨x, rfl⟩)

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic




















theorem binaryWords_encoded (bs tail : List Bool) :
    binaryWords (bs.flatMap (fun b => [true, b]) ++ [false, false] ++ tail) = (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change (b :: (binaryWords (bs.flatMap (fun c => [true, c]) ++
          [false, false] ++ tail)).1,
        (binaryWords (bs.flatMap (fun c => [true, c]) ++ [false, false] ++ tail)).2) = _
      rw [ih]

theorem binaryTotal_encBin (n : ℕ) (tail : List Bool) :
    binaryTotal (encBin n ++ tail) = (n, tail) := by
  change (Word.value (binaryWords (n.bits.flatMap (fun b => [true, b]) ++
      [false, false] ++ tail)).1,
    (binaryWords (n.bits.flatMap (fun b => [true, b]) ++ [false, false] ++ tail)).2) = _
  rw [binaryWords_encoded]
  simp only [Word.value_bits]





theorem integerTotal_encInt (z : ℤ) (tail : List Bool) :
    integerTotal (encInt z ++ tail) = (z, tail) := by
  by_cases hz : z < 0
  · simp [integerTotal, encInt, hz, binaryTotal_encBin, Signed.value, abs_of_neg hz]
  · simp [integerTotal, encInt, hz, binaryTotal_encBin, Signed.value,
      abs_of_nonneg (le_of_not_gt hz)]





theorem rationalTotal_encRat (q : ℚ) (tail : List Bool) :
    rationalTotal (encRat q ++ tail) = (q, tail) := by
  simp [rationalTotal, encRat, List.append_assoc, integerTotal_encInt, binaryTotal_encBin]



















theorem tupleWords_encoded (bs tail : List Bool) :
    tupleWords (bs.flatMap (fun b => [b, b]) ++ false :: true :: tail) = (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp [tupleWords, ih]





theorem requestPair_tupleCode (ω x : List Bool) :
    requestPair (tupleCode [ω, x]) = (ω, x) := by
  simp [requestPair, tupleCode, List.append_assoc, tupleWords_encoded]

end CritWinSpin.LocalTM2

end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic







end CritWinSpin.LocalTM2.Compiled

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic













theorem zip_ofFn {α β : Type} {N : ℕ} (f : Fin N → α) (g : Fin N → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simpa [List.ofFn_succ] using
        congrArg (List.cons (f 0, g 0)) (ih (fun i => f i.succ) (fun i => g i.succ))

theorem dot_ofFn {N : ℕ} (f g : Fin N → ℚ) :
    dot (List.ofFn f, List.ofFn g) = ∑ i, f i * g i := by
  rw [dot, zip_ofFn, List.map_ofFn]
  exact List.sum_ofFn

theorem matrixVector_ofFn {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (v : Fin N → ℚ) :
    matrixVector (List.ofFn (fun i => List.ofFn (A i)), List.ofFn v) =
      List.ofFn (A.mulVec v) := by
  rw [matrixVector, List.map_ofFn]
  congr 1
  funext i
  exact dot_ofFn (A i) v

def pivot (A : List (List ℚ)) : ℚ := (A.head?.getD []).head?.getD 0











end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp

theorem normalize_tv_le {α : Type} [Fintype α] (f w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hF : 0 < ∑ x, f x) (hW : 0 < ∑ x, w x) :
    tvDist (fun x => w x / ∑ y, w y) (fun x => f x / ∑ y, f y) ≤
      (∑ x, |w x - f x|) / ∑ x, f x := by
  classical
  let F := ∑ x, f x
  let W := ∑ x, w x
  have hF0 : F ≠ 0 := hF.ne'
  have hW0 : W ≠ 0 := hW.ne'
  have hpoint (x : α) :
      F * |w x / W - f x / F| ≤ |w x - f x| + (w x / W) * |F - W| := by
    have hid : F * (w x / W - f x / F) =
        (w x - f x) + (w x / W) * (F - W) := by field_simp [hF0, hW0]; ring
    calc
      F * |w x / W - f x / F| = |F * (w x / W - f x / F)| := by
        rw [abs_mul, abs_of_pos hF]
      _ ≤ |w x - f x| + |(w x / W) * (F - W)| := by rw [hid]; exact abs_add_le _ _
      _ = |w x - f x| + (w x / W) * |F - W| := by
        rw [abs_mul, abs_of_nonneg (div_nonneg (hw x) hW.le)]
  have hsum : F * (∑ x, |w x / W - f x / F|) ≤
      (∑ x, |w x - f x|) + |F - W| := by
    have hh := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpoint x
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_div] at hh
    have hnorm : (∑ x, w x) / W = 1 := div_self hW0
    simpa only [hnorm, one_mul] using hh
  have hdiff : |F - W| ≤ ∑ x, |w x - f x| := by
    change |(∑ x, f x) - ∑ x, w x| ≤ _
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp only [abs_sub_comm])
  unfold tvDist
  change (∑ x, |w x / W - f x / F|) / 2 ≤ (∑ x, |w x - f x|) / F
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hF]
  nlinarith

theorem normalize_tv_of_uniform_error {α : Type} [Fintype α]
    (f w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hF : 0 < ∑ x, f x) (hW : 0 < ∑ x, w x)
    (d : ℝ) (herr : ∀ x, |w x - f x| ≤ d) :
    tvDist (fun x => w x / ∑ y, w y) (fun x => f x / ∑ y, f y) ≤
      (Fintype.card α : ℝ) * d / ∑ x, f x := by
  apply (normalize_tv_le f w hw hF hW).trans
  apply div_le_div_of_nonneg_right _ hF.le
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => herr x)

namespace DyadicRounding

noncomputable def floorCounts {α : Type} (p : α → ℝ) (T : ℕ) (a : α) : ℕ :=
  ⌊(T : ℝ) * p a⌋₊

noncomputable def floorTotal {α : Type} [Fintype α] (p : α → ℝ) (T : ℕ) : ℕ :=
  ∑ a, floorCounts p T a

noncomputable def deficit {α : Type} [Fintype α] (p : α → ℝ) (T : ℕ) : ℕ :=
  T - floorTotal p T

open Classical in
noncomputable def counts {α : Type} [Fintype α] (p : α → ℝ) (T : ℕ) (a₀ a : α) : ℕ :=
  floorCounts p T a + if a = a₀ then deficit p T else 0

theorem floorTotal_le {α : Type} [Fintype α] (p : α → ℝ) (hp : IsDistribution p) (T : ℕ) :
    floorTotal p T ≤ T := by
  have hs := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg T) (hp.1 a))
  rw [← Finset.mul_sum, hp.2, mul_one] at hs
  exact_mod_cast hs

theorem counts_total {α : Type} [Fintype α] (p : α → ℝ) (hp : IsDistribution p) (T : ℕ) (a₀ : α) :
    ∑ a, counts p T a₀ a = T := by
  classical
  have hc := floorTotal_le p hp T
  simp only [counts, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change floorTotal p T + (T - floorTotal p T) = T
  omega

theorem gap_sum {α : Type} [Fintype α] (p : α → ℝ) (hp : IsDistribution p) (T : ℕ) :
    ∑ a, ((T : ℝ) * p a - floorCounts p T a) = (deficit p T : ℝ) := by
  classical
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2, mul_one]
  rw [deficit, Nat.cast_sub (floorTotal_le p hp T)]
  simp only [floorTotal, Nat.cast_sum]

theorem deficit_bound {α : Type} [Fintype α] (p : α → ℝ) (hp : IsDistribution p) (T : ℕ) :
    (deficit p T : ℝ) ≤ Fintype.card α := by
  classical
  rw [← gap_sum p hp T]
  have hh := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    (show (T : ℝ) * p a - floorCounts p T a ≤ 1 from by
      have := (Nat.lt_floor_add_one ((T : ℝ) * p a)).le
      dsimp only [floorCounts]
      linarith)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hh



theorem tv_error {α : Type} [Fintype α] (p : α → ℝ) (hp : IsDistribution p)
    (T : ℕ) (hT : 0 < T) (a₀ : α) :
    tvDist (fun a => (counts p T a₀ a : ℝ) / T) p ≤ (Fintype.card α : ℝ) / T := by
  classical
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT0 : (T : ℝ) ≠ 0 := hTr.ne'
  have hpoint (a : α) :
      (T : ℝ) * |(counts p T a₀ a : ℝ) / T - p a| ≤
        ((T : ℝ) * p a - floorCounts p T a) +
          if a = a₀ then (deficit p T : ℝ) else 0 := by
    have hgap : 0 ≤ (T : ℝ) * p a - floorCounts p T a :=
      sub_nonneg.mpr (Nat.floor_le (mul_nonneg hTr.le (hp.1 a)))
    have hid : (counts p T a₀ a : ℝ) - T * p a =
        -((T : ℝ) * p a - floorCounts p T a) +
          if a = a₀ then (deficit p T : ℝ) else 0 := by
      by_cases ha : a = a₀ <;> simp [counts, ha] <;> ring
    calc
      (T : ℝ) * |(counts p T a₀ a : ℝ) / T - p a| =
          |(T : ℝ) * ((counts p T a₀ a : ℝ) / T - p a)| := by
        rw [abs_mul, abs_of_pos hTr]
      _ =
          |(counts p T a₀ a : ℝ) - T * p a| := by
        congr 1
        field_simp [hT0]
      _ ≤ |-(T * p a - (floorCounts p T a : ℝ))| +
          |if a = a₀ then (deficit p T : ℝ) else 0| := by
        rw [hid]
        exact abs_add_le _ _
      _ = _ := by
        rw [abs_neg, abs_of_nonneg hgap, abs_of_nonneg (by split_ifs <;> positivity)]
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hpoint a
  rw [← Finset.mul_sum, Finset.sum_add_distrib, gap_sum p hp T] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  have hd := deficit_bound p hp T
  unfold tvDist
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hTr]
  nlinarith

end DyadicRounding

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
namespace FiniteTicket

def bucket : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, ticket => if ticket < c then 0 else 1 + bucket cs (ticket - c)

theorem bucket_lt_length (cs : List ℕ) (ticket : ℕ) (h : ticket < cs.sum) :
    bucket cs ticket < cs.length := by
  induction cs generalizing ticket with
  | nil => simp at h
  | cons c cs ih =>
      simp only [List.sum_cons] at h
      simp only [bucket, List.length_cons]
      split_ifs with hc
      · omega
      · have := ih (ticket - c) (by omega)
        omega

theorem bucket_count (cs : List ℕ) (i : ℕ) :
    (∑ ticket ∈ Finset.range cs.sum, if bucket cs ticket = i then (1 : ℕ) else 0) =
      cs[i]?.getD 0 := by
  induction cs generalizing i with
  | nil => simp
  | cons c cs ih =>
      rw [List.sum_cons, Finset.sum_range_add]
      have hfirst : (∑ ticket ∈ Finset.range c,
          if bucket (c :: cs) ticket = i then (1 : ℕ) else 0) =
          if i = 0 then c else 0 := by
        calc
          _ = ∑ _ ∈ Finset.range c, if 0 = i then (1 : ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro ticket ht
            simp only [bucket, if_pos (Finset.mem_range.mp ht)]
          _ = _ := by by_cases hi : i = 0 <;> simp [hi, eq_comm]
      rw [hfirst]
      cases i with
      | zero =>
          have hsecond : (∑ ticket ∈ Finset.range cs.sum,
              if bucket (c :: cs) (c + ticket) = 0 then (1 : ℕ) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro ticket ht
            simp [bucket, show ¬c + ticket < c by omega]
          simp [hsecond]
      | succ i =>
          have hsecond : (∑ ticket ∈ Finset.range cs.sum,
              if bucket (c :: cs) (c + ticket) = i + 1 then (1 : ℕ) else 0) =
              ∑ ticket ∈ Finset.range cs.sum, if bucket cs ticket = i then (1 : ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro ticket ht
            rw [bucket, if_neg (show ¬c + ticket < c by omega), Nat.add_sub_cancel_left]
            simp only [show 1 + bucket cs ticket = i + 1 ↔ bucket cs ticket = i by omega]
          simpa only [Nat.succ_ne_zero, if_false, zero_add, List.getElem?_cons_succ]
            using hsecond.trans (ih i)

def bitTicketEquiv (L : ℕ) : (Fin L → Bool) ≃ Fin (2 ^ L) :=
  (Equiv.piCongrRight fun _ : Fin L => finTwoEquiv.symm).trans finFunctionFinEquiv

theorem bitTicketEquiv_value (L : ℕ) (ω : Fin L → Bool) :
    (bitTicketEquiv L ω).val = ∑ i, (ω i).toNat * 2 ^ i.val := by
  rw [bitTicketEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (finTwoEquiv.symm (ω i)).val * 2 ^ i.val = (ω i).toNat * 2 ^ i.val
  cases h : ω i <;> rfl

def wordNumber : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * wordNumber bs

theorem wordNumber_ofFn (L : ℕ) (ω : Fin L → Bool) :
    wordNumber (List.ofFn ω) = ∑ i, (ω i).toNat * 2 ^ i.val := by
  induction L with
  | zero => simp [wordNumber]
  | succ L ih =>
      rw [List.ofFn_succ, wordNumber, Fin.sum_univ_succ, ih]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem bitTicket_wordNumber (L : ℕ) (ω : Fin L → Bool) :
    (bitTicketEquiv L ω).val = wordNumber (List.ofFn ω) := by
  rw [bitTicketEquiv_value, wordNumber_ofFn]

theorem unused_bits_expectation (L R : ℕ) (f : (Fin L → Bool) → ℝ) :
    (1 / (2 : ℝ) ^ (L + R)) *
        (∑ ω : Fin (L + R) → Bool, f (fun i => ω (Fin.castAdd R i))) =
      (1 / (2 : ℝ) ^ L) * ∑ ω : Fin L → Bool, f ω := by
  classical
  have hs : (∑ ω : Fin (L + R) → Bool, f (fun i => ω (Fin.castAdd R i))) =
      (2 : ℝ) ^ R * ∑ ω : Fin L → Bool, f ω := by
    calc
      _ = ∑ ω : (Fin L → Bool) × (Fin R → Bool), f ω.1 := by
        apply Fintype.sum_equiv (Fin.appendEquiv L R).symm
        intro ω
        rfl
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [Finset.mul_sum]
  rw [hs, pow_add]
  field_simp

def drawIndex {n : ℕ} (L : ℕ) (counts : Fin n → ℕ) (htotal : ∑ i, counts i = 2 ^ L)
    (ω : Fin L → Bool) : Fin n :=
  ⟨bucket (List.ofFn counts) (bitTicketEquiv L ω).val, by
    have ht : (bitTicketEquiv L ω).val < (List.ofFn counts).sum := by
      simpa only [List.sum_ofFn, htotal] using (bitTicketEquiv L ω).isLt
    simpa only [List.length_ofFn] using bucket_lt_length _ _ ht⟩

theorem drawIndex_count {n : ℕ} (L : ℕ) (counts : Fin n → ℕ)
    (htotal : ∑ i, counts i = 2 ^ L) (i : Fin n) :
    (∑ ω : Fin L → Bool, if drawIndex L counts htotal ω = i then (1 : ℕ) else 0) = counts i := by
  classical
  calc
    _ = ∑ ticket : Fin (2 ^ L),
        if bucket (List.ofFn counts) ticket.val = i.val then (1 : ℕ) else 0 := by
      apply Fintype.sum_equiv (bitTicketEquiv L)
      intro ω
      simp only [drawIndex, Fin.ext_iff]
    _ = ∑ ticket ∈ Finset.range (2 ^ L),
        if bucket (List.ofFn counts) ticket = i.val then (1 : ℕ) else 0 := by
      exact Fin.sum_univ_eq_sum_range
        (fun ticket => if bucket (List.ofFn counts) ticket = i.val then (1 : ℕ) else 0) (2 ^ L)
    _ = counts i := by
      have ht : (List.ofFn counts).sum = 2 ^ L := by simpa only [List.sum_ofFn] using htotal
      rw [← ht, bucket_count]
      simp

theorem drawIndex_law {n : ℕ} (L : ℕ) (counts : Fin n → ℕ)
    (htotal : ∑ i, counts i = 2 ^ L) (i : Fin n) :
    (1 / (2 : ℝ) ^ L) *
      (∑ ω : Fin L → Bool, if drawIndex L counts htotal ω = i then (1 : ℝ) else 0) =
        (counts i : ℝ) / (2 : ℝ) ^ L := by
  classical
  have hh := congrArg (fun n : ℕ => (n : ℝ)) (drawIndex_count L counts htotal i)
  push_cast at hh
  rw [hh]
  ring

end FiniteTicket
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic











theorem rationalFloor_correct (q : ℚ) : rationalFloor q = ⌊q⌋₊ := by
  by_cases hq : q < 0
  · simp [rationalFloor, hq, Nat.floor_of_nonpos hq.le]
  · have hq0 : 0 ≤ q := le_of_not_gt hq
    have hnum : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq0)
    have hrepr : (q.num.natAbs : ℚ) / q.den = q := by
      rw [← Int.cast_natCast, hnum, Rat.num_div_den]
    rw [rationalFloor, if_neg hq]
    calc
      q.num.natAbs / q.den = ⌊((q.num.natAbs : ℚ) / q.den)⌋₊ :=
        (Rat.natFloor_natCast_div_natCast _ _).symm
      _ = ⌊q⌋₊ := congrArg Nat.floor hrepr





theorem naturalSum_eq (xs : List ℕ) : naturalSum xs = xs.sum := by
  have hcast : (xs.map (fun n : ℕ => (n : ℚ))).sum = (xs.sum : ℚ) := by
    induction xs with
    | nil => simp
    | cons n xs ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
  rw [naturalSum, hcast, rationalFloor_correct, Nat.floor_natCast]























theorem bucketScan_state (cs : List ℕ) (i ticket : ℕ) (done : Bool) :
    (cs.foldl (fun s c => bucketStep (s, c)) (i, ticket, done)).1 =
      if done then i else i + FiniteTicket.bucket cs ticket := by
  induction cs generalizing i ticket done with
  | nil => cases done <;> simp [FiniteTicket.bucket]
  | cons c cs ih =>
      rw [List.foldl_cons]
      cases done with
      | true =>
          rw [show bucketStep ((i, ticket, true), c) = (i, ticket, true) by rfl, ih]
          simp
      | false =>
          by_cases hc : ticket < c
          · rw [show bucketStep ((i, ticket, false), c) = (i, ticket, true) by
              simp [bucketStep, hc], ih]
            simp [FiniteTicket.bucket, hc]
          · rw [show bucketStep ((i, ticket, false), c) = (i + 1, ticket - c, false) by
              simp [bucketStep, hc], ih]
            simp [FiniteTicket.bucket, hc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem bucketScan_eq (cs : List ℕ) (ticket : ℕ) :
    bucketScan (cs, ticket) = FiniteTicket.bucket cs ticket := by
  simpa [bucketScan] using bucketScan_state cs 0 ticket false







end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic















theorem clampTwo_contracts (x y : ℚ) (hy : -2 ≤ y ∧ y ≤ 2) :
    |clampTwo x - y| ≤ |x - y| := by
  unfold clampTwo
  split_ifs with hx hx
  · rw [abs_of_nonneg (by linarith : 0 ≤ 2 - y), abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
  · rw [abs_of_nonpos (by linarith : -2 - y ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · exact le_rfl

theorem roundTowardZero_error (x d : ℚ) (hd : 0 < d) : |roundTowardZero (x, d) - x| ≤ d := by
  unfold roundTowardZero
  split_ifs with hx
  · have hq : 0 ≤ -x / d := div_nonneg (neg_nonneg.mpr hx.le) hd.le
    have hlo := Nat.floor_le hq
    have hhi := (Nat.lt_floor_add_one (-x / d)).le
    rw [← rationalFloor_correct] at hlo hhi
    have hlo' := (le_div_iff₀ hd).mp hlo
    have hhi' := (div_le_iff₀ hd).mp hhi
    rw [abs_of_nonneg (by nlinarith : 0 ≤ -d * (rationalFloor (-x / d) : ℚ) - x)]
    nlinarith
  · have hq : 0 ≤ x / d := div_nonneg (le_of_not_gt hx) hd.le
    have hlo := Nat.floor_le hq
    have hhi := (Nat.lt_floor_add_one (x / d)).le
    rw [← rationalFloor_correct] at hlo hhi
    have hlo' := (le_div_iff₀ hd).mp hlo
    have hhi' := (div_le_iff₀ hd).mp hhi
    rw [abs_of_nonpos (by nlinarith : d * (rationalFloor (x / d) : ℚ) - x ≤ 0)]
    nlinarith

theorem clampedRound_error (x y d : ℚ) (hd : 0 < d) (hy : -2 ≤ y ∧ y ≤ 2) :
    |clampedRound (x, d) - y| ≤ |x - y| + d := by
  apply (clampTwo_contracts (roundTowardZero (x, d)) y hy).trans
  have hh := abs_sub_le (roundTowardZero (x, d)) x y
  have he := roundTowardZero_error x d hd
  linarith









end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic







theorem map_range_eq_ofFn {α : Type} (N : ℕ) (f : ℕ → α) :
    (List.range N).map f = List.ofFn (fun i : Fin N => f i.val) := by
  apply List.ext_getElem <;> simp

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

theorem log_one_add_gap {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ u - Real.log (1 + u) ∧ u - Real.log (1 + u) ≤ u ^ 2 := by
  have hb : 0 < 1 + u := by linarith
  have hupper := Real.log_le_sub_one_of_pos hb
  have hlower := Real.one_sub_inv_le_log_of_pos hb
  have hid : 1 - (1 + u)⁻¹ - (u - u ^ 2) = u ^ 3 / (1 + u) := by
    field_simp [hb.ne']
    ring
  have hnon : 0 ≤ 1 - (1 + u)⁻¹ - (u - u ^ 2) := by
    rw [hid]
    positivity
  constructor <;> linarith

theorem logarithmic_exp_error {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n) :
    0 ≤ x - (n : ℝ) * Real.log (1 + x / n) ∧
      x - (n : ℝ) * Real.log (1 + x / n) ≤ x ^ 2 / n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hg := log_one_add_gap (div_nonneg hx hnr.le)
  have hid : x - (n : ℝ) * Real.log (1 + x / n) =
      (n : ℝ) * (x / n - Real.log (1 + x / n)) := by field_simp [hnr.ne']
  have hpow : (n : ℝ) * (x / n) ^ 2 = x ^ 2 / n := by field_simp [hnr.ne']
  rw [hid]
  exact ⟨mul_nonneg hnr.le hg.1,
    (mul_le_mul_of_nonneg_left hg.2 hnr.le).trans_eq hpow⟩



theorem reciprocalExp_error (x : ℚ) (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n)
    (hsmall : (x : ℝ) ^ 2 / n ≤ 1) :
    0 ≤ reciprocalExp x n ∧
      |(reciprocalExp x n : ℝ) - Real.exp (-(x : ℝ))| ≤ 2 * (x : ℝ) ^ 2 / n := by
  have hxr : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : (0 : ℝ) < 1 + (x : ℝ) / n := by positivity
  obtain ⟨hd0, hd1⟩ := logarithmic_exp_error hxr n hn
  let d := (x : ℝ) - (n : ℝ) * Real.log (1 + (x : ℝ) / n)
  have hd : |d| ≤ 1 := by rw [abs_of_nonneg hd0]; exact hd1.trans hsmall
  have heq : (reciprocalExp x n : ℝ) = Real.exp (-(x : ℝ)) * Real.exp d := by
    rw [← Real.exp_add]
    have hid : -(x : ℝ) + d = -((n : ℝ) * Real.log (1 + (x : ℝ) / n)) := by dsimp [d]; ring
    rw [hid, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hbase]
    simp [reciprocalExp]
  refine ⟨by dsimp [reciprocalExp]; positivity, ?_⟩
  calc
    |(reciprocalExp x n : ℝ) - Real.exp (-(x : ℝ))| =
        Real.exp (-(x : ℝ)) * |Real.exp d - 1| := by
      rw [heq, show Real.exp (-(x : ℝ)) * Real.exp d - Real.exp (-(x : ℝ)) =
        Real.exp (-(x : ℝ)) * (Real.exp d - 1) by ring,
        abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 * (2 * |d|) := mul_le_mul
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hxr))
      (Real.abs_exp_sub_one_le hd) (abs_nonneg _) zero_le_one
    _ ≤ 2 * (x : ℝ) ^ 2 / n := by
      rw [abs_of_nonneg hd0]
      simpa only [one_mul, mul_div_assoc] using
        mul_le_mul_of_nonneg_left hd1 (by norm_num : (0 : ℝ) ≤ 2)

theorem exp_neg_cutoff {x d : ℝ} (hx : 0 ≤ x) (hd : 0 < d)
    (hcut : 1 / d ≤ x) : Real.exp (-x) ≤ d := by
  have hexp := Real.add_one_le_exp x
  have hdexp : 1 / d ≤ Real.exp x := by linarith
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hd]
  simpa only [one_div] using hdexp





theorem expNegativeApprox_error (x d : ℚ) (hx : 0 ≤ x) (hd : 0 < d) (hd1 : d ≤ 1) :
    0 ≤ expNegativeApprox x d ∧
      |(expNegativeApprox x d : ℝ) - Real.exp (-(x : ℝ))| ≤ (d : ℝ) := by
  have hxr : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hdr1 : (d : ℝ) ≤ 1 := by exact_mod_cast hd1
  unfold expNegativeApprox
  split_ifs with hcut
  · refine ⟨le_rfl, ?_⟩
    simpa only [Rat.cast_zero, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)] using
      exp_neg_cutoff hxr hdr (by exact_mod_cast hcut)
  · let n := reciprocalTerms x d
    have hn : 0 < n := by dsimp [n, reciprocalTerms]; omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hceilQ := (Nat.lt_floor_add_one (2 * x ^ 2 / d)).le
    have hceil : 2 * (x : ℝ) ^ 2 / d ≤ (n : ℝ) := by
      have hh : 2 * x ^ 2 / d ≤ (n : ℚ) := by
        dsimp [n, reciprocalTerms]
        exact hceilQ.trans (by norm_cast; omega)
      exact_mod_cast hh
    have hscale : 2 * (x : ℝ) ^ 2 ≤ (d : ℝ) * n := by
      simpa only [mul_comm] using (div_le_iff₀ hdr).mp hceil
    have hsmall : (x : ℝ) ^ 2 / n ≤ 1 := by
      rw [div_le_iff₀ hnr]
      nlinarith [mul_le_mul_of_nonneg_right hdr1 hnr.le]
    obtain ⟨hpos, herr⟩ := reciprocalExp_error x hx n hn hsmall
    refine ⟨hpos, herr.trans ?_⟩
    rw [div_le_iff₀ hnr]
    exact hscale

theorem reciprocalTerms_bound (x d : ℚ) (hx : 0 ≤ x) (hd : 0 < d)
    (hcut : x < 1 / d) :
    (reciprocalTerms x d : ℝ) ≤ 2 / (d : ℝ) ^ 3 + 2 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hxr : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hcutr : (x : ℝ) < 1 / d := by exact_mod_cast hcut
  have harg : (0 : ℚ) ≤ 2 * x ^ 2 / d := by positivity
  have hceilQ := Nat.floor_le harg
  have hceil : (reciprocalTerms x d : ℝ) ≤ 2 * (x : ℝ) ^ 2 / d + 2 := by
    dsimp only [reciprocalTerms]
    have hc : (⌊2 * x ^ 2 / d⌋₊ : ℝ) ≤ 2 * (x : ℝ) ^ 2 / d := by exact_mod_cast hceilQ
    push_cast
    linarith
  apply hceil.trans
  have hsq : (x : ℝ) ^ 2 ≤ (1 / (d : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hxr hcutr.le 2
  have hdiv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)) hdr.le
  have heq : 2 * (1 / (d : ℝ)) ^ 2 / d = 2 / (d : ℝ) ^ 3 := by field_simp
  rw [heq] at hdiv
  linarith

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic







theorem exponentialTerms_eq (x d : ℚ) : exponentialTerms (x, d) = reciprocalTerms x d := by
  simp only [exponentialTerms, rationalFloor_correct, reciprocalTerms]





theorem expWithFuel_eq (x d : ℚ) (fuel : List Unit)
    (hfuel : reciprocalTerms x d ≤ fuel.length) :
    expWithFuel ((x, d), fuel) = expNegativeApprox x d := by
  simp only [expWithFuel, exponentialTerms_eq, expNegativeApprox]
  split_ifs
  · rfl
  · simp [List.map_const', List.length_take, Nat.min_eq_left hfuel, List.prod_replicate,
      reciprocalExp, one_div]



theorem expWithFuel_eq_uniform (x d : ℚ) (hx : 0 ≤ x) (hd : 0 < d)
    (fuel : List Unit) (hfuel : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    expWithFuel ((x, d), fuel) = expNegativeApprox x d := by
  by_cases hcut : 1 / d ≤ x
  · simp only [expWithFuel, expNegativeApprox, if_pos hcut]
  · apply expWithFuel_eq
    have hh := (reciprocalTerms_bound x d hx hd (lt_of_not_ge hcut)).trans hfuel
    exact_mod_cast hh



end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2



theorem weightDenominatorBound_positive (S : SpinLaw) : 0 < weightDenominatorBound S := by
  dsimp [weightDenominatorBound]
  omega

theorem spin_weight_bounds (S : SpinLaw) (a : ℚ) (ha : a ∈ S.A) :
    1 / (weightDenominatorBound S : ℚ) ≤ S.ρ a ∧ S.ρ a ≤ 1 := by
  have hp := S.pos a ha
  have hD := weightDenominatorBound_positive S
  have hden : (S.ρ a).den ≤ weightDenominatorBound S := by
    have hh := Finset.single_le_sum (f := fun x => (S.ρ x).den) (fun x _ => Nat.zero_le _) ha
    dsimp only [weightDenominatorBound]
    omega
  have hnum0 : 0 ≤ (S.ρ a).num := Rat.num_nonneg.mpr hp.le
  have hnumne : (S.ρ a).num ≠ 0 := by
    intro he
    have hz : S.ρ a = 0 := Rat.num_eq_zero.mp he
    linarith
  have hnum : (1 : ℤ) ≤ (S.ρ a).num := by omega
  refine ⟨?_, ?_⟩
  · calc
      1 / (weightDenominatorBound S : ℚ) ≤ 1 / ((S.ρ a).den : ℚ) :=
        one_div_le_one_div_of_le (by exact_mod_cast (S.ρ a).den_pos) (by exact_mod_cast hden)
      _ ≤ ((S.ρ a).num : ℚ) / (S.ρ a).den :=
        div_le_div_of_nonneg_right (by exact_mod_cast hnum) (by positivity)
      _ = S.ρ a := Rat.num_div_den _
  · have hh := Finset.single_le_sum (f := S.ρ) (fun x hx => (S.pos x hx).le) ha
    simpa only [S.sum_one] using hh

def configBaseWeight (S : SpinLaw) {N : ℕ} (x : Config S (Fin N)) : ℚ :=
  ∏ i, S.ρ (x i).1

theorem configBaseWeight_bounds (S : SpinLaw) {N : ℕ} (x : Config S (Fin N)) :
    (1 / (weightDenominatorBound S : ℚ)) ^ N ≤ configBaseWeight S x ∧
      0 < configBaseWeight S x ∧ configBaseWeight S x ≤ 1 := by
  have hD : (0 : ℚ) < weightDenominatorBound S := by
    exact_mod_cast weightDenominatorBound_positive S
  have hlow : (∏ _ : Fin N, 1 / (weightDenominatorBound S : ℚ)) ≤
      ∏ i : Fin N, S.ρ (x i).1 :=
    Finset.prod_le_prod (fun _ _ => by positivity)
      (fun i _ => (spin_weight_bounds S (x i).1 (x i).2).1)
  have hpos : 0 < ∏ i : Fin N, S.ρ (x i).1 :=
    Finset.prod_pos (fun i _ => S.pos (x i).1 (x i).2)
  have hupp : (∏ i : Fin N, S.ρ (x i).1) ≤ ∏ _ : Fin N, (1 : ℚ) :=
    Finset.prod_le_prod (fun i _ => (S.pos (x i).1 (x i).2).le)
      (fun i _ => (spin_weight_bounds S (x i).1 (x i).2).2)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, configBaseWeight] using
    And.intro hlow (And.intro hpos hupp)

theorem prodRho_cast (S : SpinLaw) {N : ℕ} (x : Config S (Fin N)) :
    prodRho S x = (configBaseWeight S x : ℝ) := by
  simp [prodRho, configBaseWeight]

def energyRational {S : SpinLaw} {N : ℕ} (I : Inst N) (x : Config S (Fin N)) : ℚ :=
  (1 / 2) * ∑ i, ∑ j, I.1 i j * (x i).1 * (x j).1 + ∑ i, I.2 i * (x i).1

theorem energyRational_cast {S : SpinLaw} {N : ℕ} (I : Inst N) (x : Config S (Fin N)) :
    energy (castM I.1) (castV I.2) (spinVal x) = (energyRational I x : ℝ) := by
  simp [energy, castM, castV, spinVal, energyRational]

theorem gibbs_rational_energy {S : SpinLaw} {N : ℕ} (I : Inst N) (x : Config S (Fin N)) :
    gibbs S (castM I.1) (castV I.2) x =
      (Real.exp (energyRational I x : ℝ) * (configBaseWeight S x : ℝ)) /
        ∑ y, Real.exp (energyRational I y : ℝ) * (configBaseWeight S y : ℝ) := by
  simp only [gibbs, gibbsWeight, energyRational_cast, prodRho_cast]

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section







theorem naturalProduct_eq (xs : List ℕ) : naturalProduct xs = xs.prod := by
  have hh : (xs.map (fun n : ℕ => (n : ℚ))).prod = (xs.prod : ℚ) := by
    induction xs with
    | nil => simp
    | cons n xs ih => simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
  rw [naturalProduct, hh, rationalFloor_correct, Nat.floor_natCast]





theorem baseDigits_correct (q k : ℕ) (fuel : List Unit) :
    baseDigits ((q, k), fuel) =
      List.ofFn (fun i : Fin fuel.length => k / q ^ i.val % q) := by
  apply List.ext_getElem
  · simp [baseDigits]
  · intro i hi hj
    have hir : i < fuel.length := by simpa [baseDigits] using hi
    simp [baseDigits, naturalProduct_eq, List.map_const', List.length_take,
      Nat.min_eq_left hir.le, List.prod_replicate]



noncomputable def alphabetEquiv (S : SpinLaw) :
    Fin (alphabet S).length ≃ {a : ℚ // a ∈ S.A} :=
  (List.Nodup.getEquiv (alphabet S) S.A.nodup_toList).trans
    (Equiv.subtypeEquivRight (fun a : ℚ => show a ∈ alphabet S ↔ a ∈ S.A from Finset.mem_toList))

noncomputable def configIndexEquiv (S : SpinLaw) (N : ℕ) :
    Fin ((alphabet S).length ^ N) ≃ Config S (Fin N) :=
  finFunctionFinEquiv.symm.trans (Equiv.piCongrRight (fun _ : Fin N => alphabetEquiv S))



theorem alphabet_getD (S : SpinLaw) (i : Fin (alphabet S).length) :
    ((alphabet S)[i.val]?).getD 0 = ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ) := by
  rw [List.getElem?_eq_getElem i.isLt]
  rfl





theorem configurationValues_correct (S : SpinLaw) (fuel : List Unit)
    (k : Fin ((alphabet S).length ^ fuel.length)) :
    configurationValues S (fuel, k.val) =
      List.ofFn (fun i => (((configIndexEquiv S fuel.length k) i : ℚ))) := by
  rw [configurationValues, baseDigits_correct, List.map_ofFn]
  congr 1
  funext i
  let digit : Fin (alphabet S).length := finFunctionFinEquiv.symm k i
  have hv : digit.val = k.val / (alphabet S).length ^ i.val % (alphabet S).length := rfl
  change ((alphabet S)[k.val / (alphabet S).length ^ i.val % (alphabet S).length]?).getD 0 = _
  rw [← hv, alphabet_getD S digit]
  rfl





theorem enumerationValues_correct (S : SpinLaw) (sites : List Unit) (fuel : List Bool)
    (hfuel : (alphabet S).length ^ sites.length ≤ fuel.length) :
    enumerationValues S (sites, fuel) =
      List.ofFn (fun k => List.ofFn (fun i => (((configIndexEquiv S sites.length k) i : ℚ)))) := by
  have hc : naturalProduct (sites.map (fun _ => (alphabet S).length)) =
      (alphabet S).length ^ sites.length := by
    simp [naturalProduct_eq, List.map_const', List.prod_replicate]
  unfold enumerationValues
  rw [hc]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take,
      Nat.min_eq_left hfuel, List.length_ofFn]
  · intro i hi hj
    have hir : i < (alphabet S).length ^ sites.length := by
      simpa only [List.length_map, List.length_range, List.length_take, Nat.min_eq_left hfuel] using hi
    simpa only [List.length_take, Nat.min_eq_left hfuel, List.getElem_map,
      List.getElem_range, List.getElem_ofFn] using
      configurationValues_correct S sites ⟨i, hir⟩





theorem energyFromLists_correct {S : SpinLaw} {N : ℕ} (I : Inst N) (x : Config S (Fin N)) :
    energyFromLists ((List.ofFn (fun i => List.ofFn (I.1 i)), List.ofFn I.2),
      List.ofFn (fun i => (x i).1)) = energyRational I x := by
  simp only [energyFromLists, matrixVector_ofFn, dot_ofFn, energyRational]
  have hquad : (∑ i, (x i).1 * (I.1.mulVec (fun j => (x j).1)) i) =
      ∑ i, ∑ j, I.1 i j * (x i).1 * (x j).1 := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hquad]







theorem lookupWeight_correct (S : SpinLaw) (a : ℚ) (ha : a ∈ S.A) : lookupWeight S a = S.ρ a := by
  let p : ℚ × ℚ → Bool := fun r => decide (r.1 = a)
  have hmem : (a, S.ρ a) ∈ spinTable S := by
    apply List.mem_map.mpr
    exact ⟨a, Finset.mem_toList.mpr ha, rfl⟩
  have hex : ∃ r ∈ spinTable S, p r := ⟨(a, S.ρ a), hmem, by simp [p]⟩
  have hi : (spinTable S).findIdx p < (spinTable S).length := List.findIdx_lt_length_of_exists hex
  have hmatch : ((spinTable S)[(spinTable S).findIdx p]).1 = a := by
    have hh := List.findIdx_getElem (p := p) (w := hi)
    simpa only [p, decide_eq_true_eq] using hh
  have hentry : (spinTable S)[(spinTable S).findIdx p] ∈ spinTable S := List.getElem_mem hi
  obtain ⟨b, hb, hpair⟩ := List.mem_map.mp hentry
  have hbval : b = a := by
    have hh := congrArg Prod.fst hpair
    exact hh.trans hmatch
  have hweight := congrArg Prod.snd hpair
  change (((spinTable S)[(spinTable S).findIdx p]?).getD (0, 0)).2 = _
  rw [List.getElem?_eq_getElem hi]
  simpa only [Option.getD_some, hbval] using hweight.symm





theorem baseWeightFromValues_correct {S : SpinLaw} {N : ℕ} (x : Config S (Fin N)) :
    baseWeightFromValues S (List.ofFn (fun i => (x i).1)) = configBaseWeight S x := by
  simp only [baseWeightFromValues, List.map_ofFn, List.prod_ofFn, configBaseWeight]
  apply Finset.prod_congr rfl
  intro i _
  exact lookupWeight_correct S (x i).1 (x i).2

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC

open Classical in
theorem outLaw_reclock {α : Type} (M : RandMachine) (x : Str) (dec : Str → Option α)
    (y : Option α) (K : ℕ) (hK : M.coins x = K) :
    outLaw M x dec y = (1 / (2 : ℝ) ^ K) *
      ∑ ω : Fin K → Bool,
        if dec (M.run (tupleCode [List.ofFn ω, x])) = y then (1 : ℝ) else 0 := by
  cases hK
  rfl

theorem table_machine_law {n : ℕ} {α : Type} (e : Fin n ≃ α)
    (M : RandMachine) (x : Str) (dec : Str → Option α)
    (L R : ℕ) (counts : Fin n → ℕ) (htotal : ∑ i, counts i = 2 ^ L)
    (hcoins : M.coins x = L + R)
    (hout : ∀ ω : Fin (L + R) → Bool,
      dec (M.run (tupleCode [List.ofFn ω, x])) =
        some (e (FiniteTicket.drawIndex L counts htotal (fun i => ω (Fin.castAdd R i))))) :
    outLaw M x dec =
      (fun y => Option.elim y 0 (fun a => (counts (e.symm a) : ℝ) / (2 : ℝ) ^ L)) := by
  classical
  funext y
  rw [outLaw_reclock M x dec y (L + R) hcoins]
  cases y with
  | none => simp [hout]
  | some a =>
      simp only [hout, Option.some.injEq, Equiv.apply_eq_iff_eq_symm_apply, Option.elim_some]
      rw [FiniteTicket.unused_bits_expectation L R
        (fun ω => if FiniteTicket.drawIndex L counts htotal ω = e.symm a then (1 : ℝ) else 0)]
      exact FiniteTicket.drawIndex_law L counts htotal (e.symm a)

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic









theorem maximumQ_eq_max (xs : List ℚ) (hx : xs ≠ []) : maximumQ xs = xs.max hx := by
  cases xs with
  | nil => contradiction
  | cons a xs =>
      change (a :: xs).foldl max a = _
      rw [List.foldl_max_eq_max hx, max_eq_right (List.le_max_of_mem (by simp : a ∈ a :: xs))]

theorem maximumQ_mem (xs : List ℚ) (hx : xs ≠ []) : maximumQ xs ∈ xs := by
  rw [maximumQ_eq_max xs hx]
  exact List.max_mem hx

theorem le_maximumQ (xs : List ℚ) (a : ℚ) (ha : a ∈ xs) : a ≤ maximumQ xs := by
  rw [maximumQ_eq_max xs (List.ne_nil_of_mem ha)]
  exact List.le_max_of_mem ha


















theorem tableCapacity_bound (n m : ℕ) : 4 * n * m ≤ tableCapacity (n, m) := by
  have hh := (Nat.lt_size_self (4 * n * m)).le
  apply hh.trans
  exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _)

theorem tableRounding_error_bound (n m : ℕ) (hm : 0 < m) :
    (n : ℝ) / (2 : ℝ) ^ tableBits (n, m) ≤ 1 / (4 * (m : ℝ)) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < 4 * m)]
  have hh := tableCapacity_bound n m
  have hr : 4 * (n : ℝ) * m ≤ (2 : ℝ) ^ tableBits (n, m) := by
    exact_mod_cast hh
  nlinarith







end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary IsingLTL.BeliefProp

theorem rationalFloor_real (q : ℚ) : rationalFloor q = ⌊(q : ℝ)⌋₊ := by
  rw [rationalFloor_correct, ← Int.floor_toNat, ← Int.floor_toNat, Rat.floor_cast]

theorem normalizedRationals_ofFn {n : ℕ} (w : Fin n → ℚ) :
    normalizedRationals (List.ofFn w) = List.ofFn (fun i => w i / ∑ j, w j) := by
  simp only [normalizedRationals, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem quantizedCounts_ofFn {n : ℕ} (w : Fin (n + 1) → ℚ) (T : ℕ) :
    quantizedCounts (List.ofFn w, T) =
      List.ofFn (DyadicRounding.counts
        (fun i => (w i : ℝ) / ∑ j, (w j : ℝ)) T 0) := by
  classical
  have hc : ((normalizedRationals (List.ofFn w)).map
      (fun q => rationalFloor ((T : ℚ) * q))) =
      List.ofFn (DyadicRounding.floorCounts
        (fun i => (w i : ℝ) / ∑ j, (w j : ℝ)) T) := by
    rw [normalizedRationals_ofFn, List.map_ofFn]
    congr 1
    funext i
    change rationalFloor ((T : ℚ) * (w i / ∑ j, w j)) = _
    rw [rationalFloor_real]
    simp [DyadicRounding.floorCounts]
  simp only [quantizedCounts, hc, naturalSum_eq, List.sum_ofFn]
  simp only [List.ofFn_succ, List.isEmpty_cons, Bool.false_eq_true, ite_false,
    List.head?_cons, Option.getD_some, List.tail_cons]
  simp [DyadicRounding.counts, DyadicRounding.deficit, DyadicRounding.floorTotal]

theorem wordValue_wordNumber (xs : List Bool) : Word.value xs = FiniteTicket.wordNumber xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [Word.value, FiniteTicket.wordNumber, ih]

theorem sampleFiniteTable_ofFn {n : ℕ} (v : Fin n → List ℚ)
    (L : ℕ) (cs : Fin n → ℕ) (htotal : ∑ i, cs i = 2 ^ L) (ω : Fin L → Bool) :
    sampleFiniteTable ((List.ofFn v, List.ofFn cs), List.ofFn ω) =
      v (FiniteTicket.drawIndex L cs htotal ω) := by
  unfold sampleFiniteTable
  rw [bucketScan_eq, wordValue_wordNumber, ← FiniteTicket.bitTicket_wordNumber]
  have hb := (FiniteTicket.drawIndex L cs htotal ω).isLt
  change FiniteTicket.bucket (List.ofFn cs) (FiniteTicket.bitTicketEquiv L ω).val < n at hb
  simp only [List.getElem?_ofFn, hb, dite_true, Option.getD_some]
  rfl





end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
noncomputable section















end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp

theorem expNegativeApprox_zero (d : ℚ) (hd : 0 < d) : expNegativeApprox 0 d = 1 := by
  have hcut : ¬1 / d ≤ (0 : ℚ) := not_le.mpr (by positivity)
  simp [expNegativeApprox, hcut, reciprocalExp, reciprocalTerms, hd]

theorem shifted_exponential_normalize {α : Type} [Fintype α] (E ρ : α → ℝ) (U : ℝ) :
    (fun x => (Real.exp (E x - U) * ρ x) / ∑ y, Real.exp (E y - U) * ρ y) =
      (fun x => (Real.exp (E x) * ρ x) / ∑ y, Real.exp (E y) * ρ y) := by
  funext x
  have heq (y : α) : Real.exp (E y - U) * ρ y = Real.exp (-U) * (Real.exp (E y) * ρ y) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  simp only [heq, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

def enumeratedWeights {α : Type} (E ρ : α → ℚ) (U d : ℚ) (x : α) : ℚ :=
  ρ x * expNegativeApprox (U - E x) d

theorem enumeratedWeights_tv {α : Type} [Fintype α]
    (E ρ : α → ℚ) (U d : ℚ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hρ : ∀ x, 0 < ρ x ∧ ρ x ≤ 1) (hU : ∀ x, E x ≤ U)
    (xstar : α) (hstar : E xstar = U) :
    tvDist
      (fun x => (enumeratedWeights E ρ U d x : ℝ) / ∑ y, (enumeratedWeights E ρ U d y : ℝ))
      (fun x => (Real.exp (E x : ℝ) * (ρ x : ℝ)) /
        ∑ y, Real.exp (E y : ℝ) * (ρ y : ℝ)) ≤
      (Fintype.card α : ℝ) * d / (ρ xstar : ℝ) := by
  classical
  let f : α → ℝ := fun x => Real.exp (-(U - E x : ℚ) : ℝ) * (ρ x : ℝ)
  let w : α → ℝ := fun x => (enumeratedWeights E ρ U d x : ℝ)
  have hρpos (x : α) : (0 : ℝ) < ρ x := by exact_mod_cast (hρ x).1
  have hwpos (x : α) : 0 ≤ w x := by
    dsimp only [w, enumeratedWeights]
    push_cast
    have he := (expNegativeApprox_error (U - E x) d (sub_nonneg.mpr (hU x)) hd hd1).1
    exact mul_nonneg (hρpos x).le (by exact_mod_cast he)
  have hfpos (x : α) : 0 < f x := mul_pos (Real.exp_pos _) (hρpos x)
  have hfstar : f xstar = (ρ xstar : ℝ) := by simp [f, hstar]
  have hwstar : w xstar = (ρ xstar : ℝ) := by
    simp [w, enumeratedWeights, hstar, expNegativeApprox_zero d hd]
  have hFbound : (ρ xstar : ℝ) ≤ ∑ x, f x := by
    rw [← hfstar]
    exact Finset.single_le_sum (fun x _ => (hfpos x).le) (Finset.mem_univ xstar)
  have hWbound : (ρ xstar : ℝ) ≤ ∑ x, w x := by
    rw [← hwstar]
    exact Finset.single_le_sum (fun x _ => hwpos x) (Finset.mem_univ xstar)
  have hF : 0 < ∑ x, f x := (hρpos xstar).trans_le hFbound
  have hW : 0 < ∑ x, w x := (hρpos xstar).trans_le hWbound
  have herr (x : α) : |w x - f x| ≤ (d : ℝ) := by
    have happrox := (expNegativeApprox_error (U - E x) d (sub_nonneg.mpr (hU x)) hd hd1).2
    have hρ1 : (ρ x : ℝ) ≤ 1 := by exact_mod_cast (hρ x).2
    calc
      |w x - f x| = (ρ x : ℝ) *
          |(expNegativeApprox (U - E x) d : ℝ) - Real.exp (-(U - E x : ℚ) : ℝ)| := by
        dsimp only [w, f, enumeratedWeights]
        push_cast
        rw [mul_comm (Real.exp _) _, ← mul_sub, abs_mul, abs_of_pos (hρpos x)]
      _ ≤ (ρ x : ℝ) * d := mul_le_mul_of_nonneg_left happrox (hρpos x).le
      _ ≤ (d : ℝ) := by
        have hdr : (0 : ℝ) ≤ d := by exact_mod_cast hd.le
        nlinarith
  have htv := normalize_tv_of_uniform_error f w hwpos hF hW (d : ℝ) herr
  have hden : (Fintype.card α : ℝ) * d / ∑ x, f x ≤
      (Fintype.card α : ℝ) * d / (ρ xstar : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (hρpos xstar) hFbound
  have hf : (fun x => f x / ∑ y, f y) =
      (fun x => (Real.exp (E x : ℝ) * (ρ x : ℝ)) /
        ∑ y, Real.exp (E y : ℝ) * (ρ y : ℝ)) := by
    have heq : f = fun x => Real.exp ((E x : ℝ) - U) * (ρ x : ℝ) := by
      funext x
      dsimp only [f]
      congr 2
      push_cast
      ring
    rw [heq]
    exact shifted_exponential_normalize (fun x => (E x : ℝ)) (fun x => (ρ x : ℝ)) (U : ℝ)
  rw [← hf]
  exact htv.trans hden

theorem tv_triangle {α : Type} [Fintype α] (p q r : α → ℝ) :
    tvDist p r ≤ tvDist p q + tvDist q r := by
  have hh : (∑ x, |p x - r x|) ≤ (∑ x, |p x - q x|) + ∑ x, |q x - r x| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    exact abs_sub_le _ _ _
  unfold tvDist
  linarith

theorem bounded_mean_tv {α : Type} [Fintype α] (f p q : α → ℝ) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C) :
    |(∑ x, f x * p x) - ∑ x, f x * q x| ≤ 2 * C * tvDist p q := by
  classical
  rw [← Finset.sum_sub_distrib]
  have hh : |∑ x, (f x * p x - f x * q x)| ≤ C * ∑ x, |p x - q x| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)
  unfold tvDist
  nlinarith

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp
open CritWinSpin.Implementation.EnvelopeAnalysis





theorem phiDerivative_mean (S : SpinLaw) (t : ℝ) :
    (∑ a : {a : ℚ // a ∈ S.A}, (a.1 : ℝ) *
      ((Real.exp (t * (a.1 : ℝ)) * (S.ρ a.1 : ℝ)) /
        ∑ b : {b : ℚ // b ∈ S.A}, Real.exp (t * (b.1 : ℝ)) * (S.ρ b.1 : ℝ))) =
      deriv (phi S) t := by
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div, deriv_phi_eq, mgf]
  congr 1
  · calc
      _ = ∑ a ∈ S.A, (a : ℝ) * (Real.exp (t * (a : ℝ)) * (S.ρ a : ℝ)) :=
        Finset.sum_coe_sort S.A (fun a : ℚ => (a : ℝ) * (Real.exp (t * (a : ℝ)) * (S.ρ a : ℝ)))
      _ = _ := by apply Finset.sum_congr rfl; intro a _; ring
  · calc
      _ = ∑ a ∈ S.A, Real.exp (t * (a : ℝ)) * (S.ρ a : ℝ) :=
        Finset.sum_coe_sort S.A (fun a : ℚ => Real.exp (t * (a : ℝ)) * (S.ρ a : ℝ))
      _ = _ := by apply Finset.sum_congr rfl; intro a _; ring

theorem phiDerivativeApprox_error (S : SpinLaw) (t d : ℚ) (ht : 0 ≤ t)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    |(phiDerivativeApprox S t d : ℝ) - deriv (phi S) (t : ℝ)| ≤
      2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ) := by
  classical
  let E : {a : ℚ // a ∈ S.A} → ℚ := fun a => t * a.1
  let ρ : {a : ℚ // a ∈ S.A} → ℚ := fun a => S.ρ a.1
  let aplus : {a : ℚ // a ∈ S.A} := ⟨1, S.one_mem⟩
  have hρ : ∀ a, 0 < ρ a ∧ ρ a ≤ 1 := fun a =>
    ⟨S.pos a.1 a.2, (spin_weight_bounds S a.1 a.2).2⟩
  have hU : ∀ a, E a ≤ t := by
    intro a
    have ha := (S.mem_Icc a.1 a.2).2
    dsimp only [E]
    nlinarith
  have hstar : E aplus = t := by simp [E, aplus]
  let w : {a : ℚ // a ∈ S.A} → ℝ := fun a => (enumeratedWeights E ρ t d a : ℝ)
  let p : {a : ℚ // a ∈ S.A} → ℝ := fun a => w a / ∑ b, w b
  let q : {a : ℚ // a ∈ S.A} → ℝ := fun a =>
    (Real.exp (E a : ℝ) * (ρ a : ℝ)) / ∑ b, Real.exp (E b : ℝ) * (ρ b : ℝ)
  have htv : tvDist p q ≤ (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ) :=
    enumeratedWeights_tv E ρ t d hd hd1 hρ hU aplus hstar
  have hmean := bounded_mean_tv (fun a : {a : ℚ // a ∈ S.A} => (a.1 : ℝ)) p q 1 (by
    intro a
    obtain ⟨hlo, hhi⟩ := S.mem_Icc a.1 a.2
    rw [abs_le]
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi)
  have hpmean : (∑ a : {a : ℚ // a ∈ S.A}, (a.1 : ℝ) * p a) =
      (phiDerivativeApprox S t d : ℝ) := by
    simp only [phiDerivativeApprox, Rat.cast_div, Rat.cast_sum, Rat.cast_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    change (a.1 : ℝ) * ((tiltApproxWeight S t d a : ℝ) / ∑ b, (tiltApproxWeight S t d b : ℝ)) = _
    ring
  have hqmean : (∑ a : {a : ℚ // a ∈ S.A}, (a.1 : ℝ) * q a) =
      deriv (phi S) (t : ℝ) := by
    simpa only [q, E, ρ, Rat.cast_mul] using phiDerivative_mean S (t : ℝ)
  rw [hpmean, hqmean] at hmean
  have hm := mul_le_mul_of_nonneg_left htv (by norm_num : (0 : ℝ) ≤ 2)
  apply hmean.trans
  convert hm using 1 <;> ring

theorem deriv_phis_min_nonneg (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t : ℝ) (ht : 0 ≤ t) : deriv (phis S s) t = min (t / s) (deriv (phi S) t) := by
  obtain ⟨a, ha, hroot, hcross, _, hasOf⟩ := asOf_props_direct S hS hs
  have hs0 : 0 < s := (tau_pos S).trans hs
  have hq (u : ℝ) : deriv (phis S s) u = if |u| ≤ a then u / s else deriv (phi S) u := by
    rw [(hasDerivAt_phis_direct S hS hs u).deriv, hasOf]
  have hroot' : a / s = deriv (phi S) a := by
    rw [div_eq_iff hs0.ne']
    nlinarith
  by_cases hta : t ≤ a
  · have hsmall : t / s ≤ deriv (phi S) t := by
      rcases hta.eq_or_lt with rfl | hlt
      · exact hroot'.le
      · rcases hcross t ht hlt with hc | hzero
        · exact hc.le
        · subst t; simp [deriv_phi_zero]
    rw [hq, abs_of_nonneg ht, if_pos hta, min_eq_left hsmall]
  · have hat : a ≤ t := (lt_of_not_ge hta).le
    have hqt : deriv (phis S s) t = deriv (phi S) t := by
      rw [hq, abs_of_nonneg ht, if_neg hta]
    have hqa : deriv (phis S s) a = a / s := by
      rw [hq, abs_of_pos ha, if_pos le_rfl]
    have hlip := (deriv_phis_mono_and_lip S hS hs hat).2
    rw [hqt, hqa] at hlip
    have hid : a / s + (1 / s) * (t - a) = t / s := by ring
    have hsmall : deriv (phi S) t ≤ t / s := by linarith
    rw [hqt, min_eq_right hsmall]

theorem deriv_phis_neg (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) (t : ℝ) :
    deriv (phis S s) (-t) = -deriv (phis S s) t := by
  have hd : HasDerivAt (phis S s) (deriv (phis S s) (-t)) (-t) :=
    (hasDerivAt_phis_direct S hS hs (-t)).differentiableAt.hasDerivAt
  have hc : HasDerivAt (fun u => phis S s (-u)) (-deriv (phis S s) (-t)) t :=
    (hd.comp t (hasDerivAt_id' t).neg).congr_deriv (by ring)
  have he : (fun u => phis S s (-u)) = phis S s := funext (phis_even S s)
  rw [he] at hc
  linarith [hc.deriv]



theorem positiveModifiedDerivativeApprox_error (S : SpinLaw) (hS : IsGHS S)
    (s t d : ℚ) (hs : tau S < (s : ℝ)) (ht : 0 ≤ t) (hd : 0 < d) (hd1 : d ≤ 1) :
    |(positiveModifiedDerivativeApprox S s t d : ℝ) - deriv (phis S (s : ℝ)) (t : ℝ)| ≤
      2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ) := by
  have he := phiDerivativeApprox_error S t d ht hd hd1
  have hmin := abs_min_sub_min_le_max ((t : ℝ) / s) (phiDerivativeApprox S t d : ℝ)
    ((t : ℝ) / s) (deriv (phi S) (t : ℝ))
  have hc : (positiveModifiedDerivativeApprox S s t d : ℝ) =
      min ((t : ℝ) / s) (phiDerivativeApprox S t d : ℝ) := by
    dsimp [positiveModifiedDerivativeApprox]
    exact_mod_cast rfl
  rw [hc, deriv_phis_min_nonneg S hS hs (t : ℝ) (by exact_mod_cast ht)]
  apply (hmin.trans_eq ?_).trans he
  simp only [sub_self, abs_zero]
  exact max_eq_right (abs_nonneg ((phiDerivativeApprox S t d : ℝ) - deriv (phi S) (t : ℝ)))

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section











theorem phiMeanWithFuel_correct (S : SpinLaw) (t d : ℚ) (ht : 0 ≤ t) (hd : 0 < d)
    (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    phiMeanWithFuel S ((t, d), fuel) = phiDerivativeApprox S t d := by
  have he (a : ℚ) (ha : a ∈ S.A) :
      expWithFuel ((t - t * a, d), fuel) = expNegativeApprox (t - t * a) d := by
    have ha1 := (S.mem_Icc a ha).2
    exact expWithFuel_eq_uniform _ _ (by nlinarith) hd fuel hf
  unfold phiMeanWithFuel tiltRecords spinTable alphabet phiDerivativeApprox tiltApproxWeight
  simp only [List.map_map, Function.comp_def, Finset.sum_map_toList]
  congr 1
  · calc
      _ = ∑ a ∈ S.A, a * (S.ρ a * expNegativeApprox (t - t * a) d) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [he a ha]
      _ = _ := (Finset.sum_coe_sort S.A
        (fun a : ℚ => a * (S.ρ a * expNegativeApprox (t - t * a) d))).symm
  · calc
      _ = ∑ a ∈ S.A, S.ρ a * expNegativeApprox (t - t * a) d := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [he a ha]
      _ = _ := (Finset.sum_coe_sort S.A
        (fun a : ℚ => S.ρ a * expNegativeApprox (t - t * a) d)).symm









theorem positiveModifiedWithFuel_correct (S : SpinLaw) (s t d : ℚ) (ht : 0 ≤ t) (hd : 0 < d)
    (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    positiveModifiedWithFuel S (s, ((t, d), fuel)) = positiveModifiedDerivativeApprox S s t d := by
  unfold positiveModifiedWithFuel rationalMin positiveModifiedDerivativeApprox
  rw [phiMeanWithFuel_correct S t d ht hd fuel hf]
  exact (min_def _ _).symm







theorem modifiedWithFuel_correct (S : SpinLaw) (s t d : ℚ) (hd : 0 < d)
    (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    modifiedWithFuel S (s, ((t, d), fuel)) = modifiedDerivativeApprox S s t d := by
  by_cases ht : t < 0
  · simp only [modifiedWithFuel, modifiedDerivativeApprox, ht, ite_true]
    rw [positiveModifiedWithFuel_correct S s (-t) d (by linarith) hd fuel hf]
  · simp only [modifiedWithFuel, modifiedDerivativeApprox, ht, ite_false]
    exact positiveModifiedWithFuel_correct S s t d (by linarith) hd fuel hf

theorem modifiedDerivativeApprox_error (S : SpinLaw) (hS : IsGHS S) (s t d : ℚ)
    (hs : tau S < (s : ℝ)) (hd : 0 < d) (hd1 : d ≤ 1) :
    |(modifiedDerivativeApprox S s t d : ℝ) - deriv (phis S s) (t : ℝ)| ≤
      2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ) := by
  by_cases ht : t < 0
  · have hh := positiveModifiedDerivativeApprox_error S hS s (-t) d hs (by linarith) hd hd1
    simp only [modifiedDerivativeApprox, ht, ite_true, Rat.cast_neg]
    rw [show (t : ℝ) = -((-t : ℚ) : ℝ) by simp,
      deriv_phis_neg S hS hs, neg_sub_neg, abs_sub_comm]
    exact hh
  · simpa only [modifiedDerivativeApprox, ht, ite_false] using
      positiveModifiedDerivativeApprox_error S hS s t d hs (by linarith) hd hd1



end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2



theorem sqrtIter_bounds (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    0 ≤ sqrtIter a n ∧ sqrtIter a n ≤ Real.sqrt a := by
  have hs0 := Real.sqrt_nonneg a
  have hs2 := Real.sq_sqrt ha
  have hs1 : Real.sqrt a ≤ 1 := (Real.sqrt_le_one).mpr ha1
  induction n with
  | zero => simp [sqrtIter, hs0]
  | succ n ih =>
      obtain ⟨hr0, hrs⟩ := ih
      have hprod : 0 ≤ (Real.sqrt a - sqrtIter a n) *
          (1 - (Real.sqrt a + sqrtIter a n) / 2) :=
        mul_nonneg (sub_nonneg.mpr hrs) (by linarith)
      have hres : 0 ≤ a - (sqrtIter a n) ^ 2 := by nlinarith
      simp only [sqrtIter]
      constructor <;> nlinarith

theorem sqrtIter_error_recurrence (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    Real.sqrt a - sqrtIter a (n + 1) ≤
      (Real.sqrt a - sqrtIter a n) - (Real.sqrt a - sqrtIter a n) ^ 2 / 2 := by
  obtain ⟨hr0, hrs⟩ := sqrtIter_bounds a ha ha1 n
  have hs2 := Real.sq_sqrt ha
  have hprod := mul_nonneg (sub_nonneg.mpr hrs) hr0
  simp only [sqrtIter]
  nlinarith

theorem decay_step (q : ℝ) (hq : 2 ≤ q) :
    2 / q - (2 / q) ^ 2 / 2 ≤ 2 / (q + 1) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q + 1 := by linarith
  field_simp
  nlinarith

theorem sqrtIter_error (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    Real.sqrt a - sqrtIter a n ≤ 2 / ((n : ℝ) + 2) := by
  have hs1 : Real.sqrt a ≤ 1 := (Real.sqrt_le_one).mpr ha1
  induction n with
  | zero => simpa [sqrtIter] using hs1
  | succ n ih =>
      have hrec := sqrtIter_error_recurrence a ha ha1 n
      obtain ⟨hr0, hrs⟩ := sqrtIter_bounds a ha ha1 n
      have he0 : 0 ≤ Real.sqrt a - sqrtIter a n := sub_nonneg.mpr hrs
      have hb0 : 0 < 2 / ((n : ℝ) + 2) := by positivity
      have hb1 : 2 / ((n : ℝ) + 2) ≤ 1 :=
        (div_le_iff₀ (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hprod := mul_nonneg (sub_nonneg.mpr ih)
        (show 0 ≤ 2 - 2 / ((n : ℝ) + 2) - (Real.sqrt a - sqrtIter a n) by linarith)
      have hmono : (Real.sqrt a - sqrtIter a n) - (Real.sqrt a - sqrtIter a n) ^ 2 / 2 ≤
          2 / ((n : ℝ) + 2) - (2 / ((n : ℝ) + 2)) ^ 2 / 2 := by nlinarith
      have hdec := decay_step ((n : ℝ) + 2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hden : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 2 + 1 := by push_cast; ring
      rw [hden]
      exact hrec.trans (hmono.trans hdec)

theorem sqrtIter_residual (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    0 ≤ a - (sqrtIter a n) ^ 2 ∧ a - (sqrtIter a n) ^ 2 ≤ 4 / ((n : ℝ) + 2) := by
  obtain ⟨hr0, hrs⟩ := sqrtIter_bounds a ha ha1 n
  have he := sqrtIter_error a ha ha1 n
  have hs2 := Real.sq_sqrt ha
  have hs1 : Real.sqrt a ≤ 1 := (Real.sqrt_le_one).mpr ha1
  have hprod := mul_nonneg (sub_nonneg.mpr hrs)
    (show 0 ≤ 2 - (Real.sqrt a + sqrtIter a n) by linarith)
  constructor
  · nlinarith
  · have : a - (sqrtIter a n) ^ 2 ≤ 2 * (Real.sqrt a - sqrtIter a n) := by nlinarith
    have he' := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)
    have hfra : 2 * (2 / ((n : ℝ) + 2)) = 4 / ((n : ℝ) + 2) := by ring
    rw [hfra] at he'
    exact this.trans he'





end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix



theorem scalar_shift_psd_spectral {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (s : ℝ) :
    (s • (1 : Matrix (Fin N) (Fin N) ℝ) - A).PosSemidef ↔
      ∀ i, hA.eigenvalues i ≤ s := by
  let U := hA.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut ℝ (Matrix (Fin N) (Fin N) ℝ) U
  have hI : F (s • (1 : Matrix (Fin N) (Fin N) ℝ)) =
      s • (1 : Matrix (Fin N) (Fin N) ℝ) := by simp [F]
  have hD : F (Matrix.diagonal hA.eigenvalues) = A := by
    simpa only [F, U, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.spectral_theorem.symm
  have heq : s • (1 : Matrix (Fin N) (Fin N) ℝ) - A =
      F (Matrix.diagonal (fun i => s - hA.eigenvalues i)) := by
    have hd : Matrix.diagonal (fun i => s - hA.eigenvalues i) =
        s • (1 : Matrix (Fin N) (Fin N) ℝ) - Matrix.diagonal hA.eigenvalues := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    rw [hd, map_sub, hI, hD]
  rw [heq]
  change ((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal (fun i => s - hA.eigenvalues i) *
      star (U : Matrix (Fin N) (Fin N) ℝ)).PosSemidef ↔ _
  rw [Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff, Matrix.posSemidef_diagonal_iff]
  simp only [sub_nonneg]







end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

noncomputable def matrixSqrtIter {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => 0
  | n + 1 => matrixSqrtIter A n + (1 / 2 : ℝ) • (A - (matrixSqrtIter A n) ^ 2)

theorem matrixSqrtIter_conj {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) (n : ℕ) :
    matrixSqrtIter (Unitary.conjStarAlgAut ℝ _ U A) n =
      Unitary.conjStarAlgAut ℝ _ U (matrixSqrtIter A n) := by
  induction n with
  | zero => simp [matrixSqrtIter]
  | succ n ih => simp only [matrixSqrtIter, ih, map_add, map_sub, map_smul, map_pow]

theorem matrixSqrtIter_diagonal {N : ℕ} (a : Fin N → ℝ) (n : ℕ) :
    matrixSqrtIter (Matrix.diagonal a) n = Matrix.diagonal (fun i => sqrtIter (a i) n) := by
  induction n with
  | zero => simp [matrixSqrtIter, sqrtIter]
  | succ n ih =>
      simp only [matrixSqrtIter, ih, Matrix.diagonal_pow, Matrix.diagonal_sub,
        ← Matrix.diagonal_smul, Matrix.diagonal_add]
      congr 1
      funext i
      simp [sqrtIter, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem unitary_conj_posSemidef {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℝ)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef) :
    (Unitary.conjStarAlgAut ℝ _ U A).PosSemidef := by
  change ((U : Matrix (Fin N) (Fin N) ℝ) * A * star (U : Matrix (Fin N) (Fin N) ℝ)).PosSemidef
  exact Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff.mpr hA

theorem matrixSqrtIter_certificates {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosSemidef) (hA1 : ((1 : Matrix (Fin N) (Fin N) ℝ) - A).PosSemidef) (n : ℕ) :
    (matrixSqrtIter A n).PosSemidef ∧
      ((1 : Matrix (Fin N) (Fin N) ℝ) - matrixSqrtIter A n).PosSemidef ∧
      (A - (matrixSqrtIter A n) ^ 2).PosSemidef ∧
      (((4 / ((n : ℝ) + 2)) • (1 : Matrix (Fin N) (Fin N) ℝ)) -
        (A - (matrixSqrtIter A n) ^ 2)).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut ℝ (Matrix (Fin N) (Fin N) ℝ) U
  let ev : Fin N → ℝ := hA.isHermitian.eigenvalues
  let r : Fin N → ℝ := fun i => sqrtIter (ev i) n
  have hev0 (i : Fin N) : 0 ≤ ev i := hA.eigenvalues_nonneg i
  have hev1 (i : Fin N) : ev i ≤ 1 := by
    exact (scalar_shift_psd_spectral A hA.isHermitian 1).mp (by simpa using hA1) i
  have hAspec : F (Matrix.diagonal ev) = A := by
    simpa only [F, U, ev, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.isHermitian.spectral_theorem.symm
  have hXspec : matrixSqrtIter A n = F (Matrix.diagonal r) := by
    rw [← hAspec, matrixSqrtIter_conj, matrixSqrtIter_diagonal]
  have hRspec : A - (matrixSqrtIter A n) ^ 2 =
      F (Matrix.diagonal (fun i => ev i - (r i) ^ 2)) := by
    rw [hXspec, ← hAspec, ← map_pow, ← map_sub,
      Matrix.diagonal_pow, ← Matrix.diagonal_sub]
    rfl
  have hDr : (Matrix.diagonal r).PosSemidef := Matrix.PosSemidef.diagonal
    (fun i => (sqrtIter_bounds (ev i) (hev0 i) (hev1 i) n).1)
  have hD1 : ((1 : Matrix (Fin N) (Fin N) ℝ) - Matrix.diagonal r).PosSemidef := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    have hr := (sqrtIter_bounds (ev i) (hev0 i) (hev1 i) n).2
    have hs : Real.sqrt (ev i) ≤ 1 := Real.sqrt_le_one.mpr (hev1 i)
    change 0 ≤ 1 - sqrtIter (ev i) n
    linarith
  have hDR : (Matrix.diagonal (fun i => ev i - (r i) ^ 2)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => (sqrtIter_residual (ev i) (hev0 i) (hev1 i) n).1)
  have hDc : (((4 / ((n : ℝ) + 2)) • (1 : Matrix (Fin N) (Fin N) ℝ)) -
      Matrix.diagonal (fun i => ev i - (r i) ^ 2)).PosSemidef := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    have hr := (sqrtIter_residual (ev i) (hev0 i) (hev1 i) n).2
    change 0 ≤ 4 / ((n : ℝ) + 2) * 1 - (ev i - sqrtIter (ev i) n ^ 2)
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hXspec]
    exact unitary_conj_posSemidef U hDr
  · have hh := unitary_conj_posSemidef U hD1
    change (F (1 - Matrix.diagonal r)).PosSemidef at hh
    rw [map_sub, map_one, ← hXspec] at hh
    exact hh
  · rw [hRspec]
    exact unitary_conj_posSemidef U hDR
  · have hh := unitary_conj_posSemidef U hDc
    change (F (((4 / ((n : ℝ) + 2)) • 1) -
      Matrix.diagonal (fun i => ev i - (r i) ^ 2))).PosSemidef at hh
    rw [map_sub, map_smul, map_one, ← hRspec] at hh
    exact hh

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

theorem psd_unit_entry_bound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosSemidef) (hA1 : ((1 : Matrix (Fin N) (Fin N) ℝ) - A).PosSemidef)
    (i j : Fin N) : |A i j| ≤ 1 := by
  have hi0 := hA.diag_nonneg (i := i)
  have hj0 := hA.diag_nonneg (i := j)
  have hi1 : A i i ≤ 1 := by
    have hh := hA1.diag_nonneg (i := i)
    simpa using hh
  have hj1 : A j j ≤ 1 := by
    have hh := hA1.diag_nonneg (i := j)
    simpa using hh
  have hsym : A j i = A i j := (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).apply i j
  have hdet : 0 ≤ A i i * A j j - A i j * A j i := by
    have hd := (hA.submatrix (![i, j] : Fin 2 → Fin N)).det_nonneg
    rw [Matrix.det_fin_two] at hd
    simpa using hd
  have hprod : A i i * A j j ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hi1 hj1 hj0 (by norm_num : (0 : ℝ) ≤ 1)
  rw [hsym] at hdet
  apply (sq_le_one_iff_abs_le_one (A i j)).mp
  nlinarith

theorem matrixSqrtIter_entry_bound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosSemidef) (hA1 : ((1 : Matrix (Fin N) (Fin N) ℝ) - A).PosSemidef)
    (n : ℕ) (i j : Fin N) : |matrixSqrtIter A n i j| ≤ 1 := by
  obtain ⟨hX, hX1, _, _⟩ := matrixSqrtIter_certificates A hA hA1 n
  exact psd_unit_entry_bound _ hX hX1 i j

theorem matrix_square_entry_difference {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ)
    (b e : ℝ) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hA : ∀ i j, |A i j| ≤ b) (hB : ∀ i j, |B i j| ≤ b)
    (hAB : ∀ i j, |A i j - B i j| ≤ e) (i j : Fin N) :
    |(A ^ 2 - B ^ 2) i j| ≤ 2 * (N : ℝ) * b * e := by
  have hterm (k : Fin N) : |A i k * A k j - B i k * B k j| ≤ 2 * b * e := by
    calc
      _ = |A i k * (A k j - B k j) + (A i k - B i k) * B k j| := by congr 1; ring
      _ ≤ |A i k * (A k j - B k j)| + |(A i k - B i k) * B k j| := abs_add_le _ _
      _ = |A i k| * |A k j - B k j| + |A i k - B i k| * |B k j| := by rw [abs_mul, abs_mul]
      _ ≤ b * e + e * b := add_le_add
        (mul_le_mul (hA i k) (hAB k j) (abs_nonneg _) hb)
        (mul_le_mul (hAB i k) (hB k j) (abs_nonneg _) he)
      _ = _ := by ring
  simp only [pow_two, Matrix.sub_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm] using hh

theorem matrix_sqrt_step_difference {N : ℕ} (J A B : Matrix (Fin N) (Fin N) ℝ)
    (b e : ℝ) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hA : ∀ i j, |A i j| ≤ b) (hB : ∀ i j, |B i j| ≤ b)
    (hAB : ∀ i j, |A i j - B i j| ≤ e) (i j : Fin N) :
    |(A + (1 / 2 : ℝ) • (J - A ^ 2)) i j -
      (B + (1 / 2 : ℝ) • (J - B ^ 2)) i j| ≤ (1 + (N : ℝ) * b) * e := by
  have hs := matrix_square_entry_difference A B b e hb he hA hB hAB i j
  have hid : (A + (1 / 2 : ℝ) • (J - A ^ 2)) i j -
      (B + (1 / 2 : ℝ) • (J - B ^ 2)) i j =
      (A i j - B i j) - (1 / 2 : ℝ) * (A ^ 2 - B ^ 2) i j := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
    ring
  rw [hid]
  have hh := abs_sub_le (A i j - B i j) 0 ((1 / 2 : ℝ) * (A ^ 2 - B ^ 2) i j)
  simp only [sub_zero, zero_sub, abs_neg] at hh
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hh
  nlinarith [hAB i j]

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open Matrix

theorem castM_addQ {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℚ) :
    castM (A + B) = castM A + castM B := by ext i j; simp [castM]

theorem castM_subQ {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℚ) :
    castM (A - B) = castM A - castM B := by ext i j; simp [castM]

theorem castM_smulQ {N : ℕ} (q : ℚ) (A : Matrix (Fin N) (Fin N) ℚ) :
    castM (q • A) = (q : ℝ) • castM A := by ext i j; simp [castM, Matrix.smul_apply]

theorem castM_mulQ {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℚ) :
    castM (A * B) = castM A * castM B := by ext i j; simp [castM, Matrix.mul_apply]



def matrixSqrtIterQ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) : ℕ → Matrix (Fin N) (Fin N) ℚ
  | 0 => 0
  | n + 1 => sqrtStepQ A (matrixSqrtIterQ A n)

theorem sqrtStepQ_cast {N : ℕ} (A X : Matrix (Fin N) (Fin N) ℚ) :
    castM (sqrtStepQ A X) = castM X + (1 / 2 : ℝ) • (castM A - (castM X) ^ 2) := by
  simp only [sqrtStepQ, castM_addQ, castM_smulQ, castM_subQ, pow_two, castM_mulQ]
  norm_num

theorem matrixSqrtIterQ_cast {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (n : ℕ) :
    castM (matrixSqrtIterQ A n) = matrixSqrtIter (castM A) n := by
  induction n with
  | zero => ext i j; simp [matrixSqrtIterQ, matrixSqrtIter, castM]
  | succ n ih => rw [matrixSqrtIterQ, sqrtStepQ_cast, ih]; rfl



theorem roundedMatrixSqrt_entry_bound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (d : ℚ) (n : ℕ) (i j : Fin N) : |(castM (roundedMatrixSqrt A d n)) i j| ≤ 2 := by
  cases n with
  | zero => simp [roundedMatrixSqrt, castM]
  | succ n =>
      change |(Compiled.clampedRound ((sqrtStepQ A (roundedMatrixSqrt A d n)) i j, d) : ℝ)| ≤ 2
      exact_mod_cast abs_le.mpr (Compiled.clampTwo_bounds
        (Compiled.roundTowardZero ((sqrtStepQ A (roundedMatrixSqrt A d n)) i j, d)))

theorem roundedMatrixSqrt_error {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : (castM A).PosSemidef)
    (hA1 : ((1 : Matrix (Fin N) (Fin N) ℝ) - castM A).PosSemidef)
    (d : ℚ) (hd : 0 < d) (n : ℕ) :
    ∀ i j, |(castM (roundedMatrixSqrt A d n)) i j - matrixSqrtIter (castM A) n i j| ≤
      (d : ℝ) * (n : ℝ) * (1 + 2 * (N : ℝ)) ^ n := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  let q : ℝ := 1 + 2 * (N : ℝ)
  have hq : 1 ≤ q := by dsimp [q]; have := Nat.cast_nonneg (α := ℝ) N; linarith
  induction n with
  | zero => intro i j; simp [roundedMatrixSqrt, matrixSqrtIter, castM]
  | succ n ih =>
      intro i j
      let Y := castM (roundedMatrixSqrt A d n)
      let X := matrixSqrtIter (castM A) n
      let e : ℝ := (d : ℝ) * (n : ℝ) * q ^ n
      have he : 0 ≤ e := by dsimp [e]; positivity
      have hX : ∀ i j, |X i j| ≤ 2 := by
        intro i j
        exact (matrixSqrtIter_entry_bound (castM A) hA hA1 n i j).trans (by norm_num)
      have hY : ∀ i j, |Y i j| ≤ 2 := roundedMatrixSqrt_entry_bound A d n
      have hdiff : ∀ i j, |Y i j - X i j| ≤ e := ih
      have hstep := matrix_sqrt_step_difference (castM A) Y X 2 e (by norm_num) he hY hX hdiff i j
      let v : ℚ := (sqrtStepQ A (roundedMatrixSqrt A d n)) i j
      let u : ℚ := matrixSqrtIterQ A (n + 1) i j
      have hu : (u : ℝ) = matrixSqrtIter (castM A) (n + 1) i j := by
        change (castM (matrixSqrtIterQ A (n + 1))) i j = _
        rw [matrixSqrtIterQ_cast]
      have hv : (v : ℝ) = (Y + (1 / 2 : ℝ) • (castM A - Y ^ 2)) i j := by
        change (castM (sqrtStepQ A (roundedMatrixSqrt A d n))) i j = _
        rw [sqrtStepQ_cast]
      have hub : -2 ≤ u ∧ u ≤ 2 := by
        have hh := matrixSqrtIter_entry_bound (castM A) hA hA1 (n + 1) i j
        rw [← hu] at hh
        have hhQ : |u| ≤ (1 : ℚ) := by exact_mod_cast hh
        obtain ⟨hl, hr⟩ := abs_le.mp hhQ
        constructor <;> linarith
      have hround := Compiled.clampedRound_error v u d hd hub
      have hroundR : |(Compiled.clampedRound (v, d) : ℝ) - (u : ℝ)| ≤ |(v : ℝ) - (u : ℝ)| + d := by
        exact_mod_cast hround
      rw [hu, hv] at hroundR
      have hideal : matrixSqrtIter (castM A) (n + 1) = X + (1 / 2 : ℝ) • (castM A - X ^ 2) := rfl
      rw [hideal] at hroundR
      have herr : |(Compiled.clampedRound (v, d) : ℝ) - matrixSqrtIter (castM A) (n + 1) i j| ≤ q * e + d := by
        rw [hideal]
        have hh := hroundR.trans (add_le_add hstep (le_rfl : (d : ℝ) ≤ (d : ℝ)))
        simpa only [q, mul_comm (N : ℝ) 2] using hh
      have hp : (d : ℝ) ≤ (d : ℝ) * q ^ (n + 1) := by
        have hpower : 1 ≤ q ^ (n + 1) := one_le_pow₀ hq
        have hh := mul_le_mul_of_nonneg_left hpower hdr.le
        simpa only [mul_one] using hh
      change |(Compiled.clampedRound (v, d) : ℝ) - matrixSqrtIter (castM A) (n + 1) i j| ≤ _
      apply herr.trans
      calc
        q * e + (d : ℝ) ≤ q * e + (d : ℝ) * q ^ (n + 1) := add_le_add le_rfl hp
        _ = (d : ℝ) * ((n + 1 : ℕ) : ℝ) * (1 + 2 * (N : ℝ)) ^ (n + 1) := by
          simp only [e, q]
          push_cast
          rw [pow_succ]
          ring

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
























theorem matrixEntry_ofFn {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (i j : Fin N) :
    matrixEntry (List.ofFn (fun i => List.ofFn (A i)), (i.val, j.val)) = A i j := by
  simp [matrixEntry, List.getElem?_eq_getElem, i.isLt, j.isLt]

theorem matrixProductEntry_ofFn {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (sites : List Unit) (hsites : sites.length = N) (i j : Fin N) :
    matrixProductEntry ((List.ofFn (fun i => List.ofFn (A i)), sites), (i.val, j.val)) =
      (A ^ 2) i j := by
  simp only [matrixProductEntry, siteNumbers, hsites]
  rw [map_range_eq_ofFn, List.sum_ofFn]
  simp only [matrixEntry_ofFn]
  simp only [pow_two, Matrix.mul_apply]

theorem roundedRootRows_ofFn {N : ℕ} (A X : Matrix (Fin N) (Fin N) ℚ)
    (sites : List Unit) (hsites : sites.length = N) (d : ℚ) :
    roundedRootRows (((List.ofFn (fun i => List.ofFn (A i)), sites), d),
      List.ofFn (fun i => List.ofFn (X i))) =
        List.ofFn (fun i => List.ofFn (fun j => clampedRound ((sqrtStepQ A X) i j, d))) := by
  simp only [roundedRootRows, siteNumbers, hsites]
  rw [map_range_eq_ofFn]
  congr 1
  funext i
  rw [map_range_eq_ofFn]
  congr 1
  funext j
  rw [matrixEntry_ofFn, matrixEntry_ofFn, matrixProductEntry_ofFn X sites hsites i j]
  simp only [sqrtStepQ, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  congr 1
  ring































theorem rootZeroRows_correct (N : ℕ) :
    rootZeroRows (List.replicate N ()) =
      List.ofFn (fun _ : Fin N => List.ofFn (fun _ : Fin N => (0 : ℚ))) := by
  simp [rootZeroRows, List.ofFn_const]

theorem rootCompute_correct {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (d : ℚ)
    (fuel : List Unit) :
    rootCompute (((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d), fuel) =
      List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d fuel.length i)) := by
  have hfold (xs : List Unit) (n : ℕ) :
      xs.foldl (fun st _ => roundedRootStep st)
        (((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d),
          List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d n i))) =
        (((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d),
          List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d (n + xs.length) i))) := by
    induction xs generalizing n with
    | nil => simp
    | cons u xs ih =>
        rw [List.foldl_cons]
        change xs.foldl (fun st _ => roundedRootStep st)
          (_, roundedRootRows (((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d),
            List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d n i)))) = _
        rw [roundedRootRows_ofFn A (roundedMatrixSqrt A d n) (List.replicate N ()) (List.length_replicate ..) d]
        change xs.foldl (fun st _ => roundedRootStep st)
          (_, List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d (n + 1) i))) = _
        rw [ih]
        simp only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  unfold rootCompute
  rw [rootZeroRows_correct]
  have hh := hfold fuel 0
  have hz : List.ofFn (fun i => List.ofFn (roundedMatrixSqrt A d 0 i)) =
      List.replicate N (List.replicate N (0 : ℚ)) := by
    change List.ofFn (fun _ : Fin N => List.ofFn (fun _ : Fin N => (0 : ℚ))) = _
    simp only [List.ofFn_const]
  rw [hz] at hh
  simpa only [Nat.zero_add, List.ofFn_const] using congrArg Prod.snd hh

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section




















def driftInputOf {N : ℕ} (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ)
    (s a d : ℚ) (fuel : List Unit) : DriftInput :=
  (((List.ofFn (fun i => List.ofFn (L i)), List.ofFn h),
    (List.replicate N (), (s, a, d))), (List.ofFn z, fuel))



theorem driftCoefficients_correct {N : ℕ} (S : SpinLaw)
    (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ) (s a d : ℚ)
    (hd : 0 < d) (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    driftCoefficients S (driftInputOf L h z s a d fuel) =
      List.ofFn (fun i => modifiedDerivativeApprox S s (L.mulVec z i + h i) d) := by
  unfold driftCoefficients driftArguments driftInputOf
  rw [matrixVector_ofFn, zip_ofFn, List.map_ofFn, List.map_ofFn]
  congr 1
  funext i
  exact modifiedWithFuel_correct S s (L.mulVec z i + h i) d hd fuel hf

theorem driftTransposeProduct_correct {N : ℕ} (S : SpinLaw)
    (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ) (s a d : ℚ)
    (hd : 0 < d) (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length)
    (i : Fin N) :
    driftTransposeProduct S (driftInputOf L h z s a d fuel, i.val) =
      ∑ j, L j i * modifiedDerivativeApprox S s (L.mulVec z j + h j) d := by
  unfold driftTransposeProduct
  rw [driftCoefficients_correct S L h z s a d hd fuel hf]
  simp only [driftInputOf, siteNumbers, List.length_replicate]
  rw [map_range_eq_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp [matrixEntry_ofFn, j.isLt]

theorem driftWithFuel_correct {N : ℕ} (S : SpinLaw)
    (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ) (s a d : ℚ)
    (hd : 0 < d) (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    driftWithFuel S (driftInputOf L h z s a d fuel) =
      List.ofFn (approximateGradient S L h z s a d) := by
  unfold driftWithFuel
  simp only [siteNumbers, driftInputOf, List.length_replicate]
  change (List.range N).map _ = _
  rw [map_range_eq_ofFn]
  congr 1
  funext i
  change (1 + a) * ((List.ofFn z)[i.val]?).getD 0 -
    driftTransposeProduct S (driftInputOf L h z s a d fuel, i.val) = _
  rw [driftTransposeProduct_correct S L h z s a d hd fuel hf i]
  simp [driftInputOf, approximateGradient, i.isLt]





end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open CritWinSpin.Implementation.EnvelopeGeometry
noncomputable section



























theorem snappedDriftWithFuel_correct {N : ℕ} (S : SpinLaw)
    (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ) (s a d snap : ℚ)
    (hd : 0 < d) (fuel : List Unit) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    snappedDriftWithFuel S (snap, driftInputOf L h z s a d fuel) =
      List.ofFn (approximateGradient S L h (fun i => roundTowardZero (z i, snap)) s a d) := by
  unfold snappedDriftWithFuel
  simp only [driftInputOf, List.map_ofFn]
  change driftWithFuel S (driftInputOf L h (fun i => roundTowardZero (z i, snap)) s a d fuel) = _
  exact driftWithFuel_correct S L h _ s a d hd fuel hf

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open MeasureTheory

def rectangleSum (g : ℝ → ℝ) (a h : ℝ) (n : ℕ) : ℝ :=
  h * ∑ i ∈ Finset.range n, g (a + (i : ℝ) * h)

theorem rectangleRule_error (g : ℝ → ℝ) (a h K : ℝ) (n : ℕ) (hh : 0 ≤ h)
    (hint : ∀ i < n, IntervalIntegrable g volume (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h))
    (hmod : ∀ i < n, ∀ x ∈ Set.Ioc (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h),
      |g x - g (a + (i : ℝ) * h)| ≤ K * h) :
    |rectangleSum g a h n - ∫ x in a..a + (n : ℝ) * h, g x| ≤ (n : ℝ) * K * h ^ 2 := by
  have hcell (i : ℕ) (hi : i < n) :
      |h * g (a + (i : ℝ) * h) -
        ∫ x in (a + (i : ℝ) * h)..(a + ((i : ℝ) + 1) * h), g x| ≤ K * h ^ 2 := by
    have hab : a + (i : ℝ) * h ≤ a + ((i : ℝ) + 1) * h := by nlinarith
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a + (i : ℝ) * h) (b := a + ((i : ℝ) + 1) * h)
      (f := fun x => g x - g (a + (i : ℝ) * h)) (C := K * h) (by
        intro x hx
        rw [Set.uIoc_of_le hab] at hx
        simpa only [Real.norm_eq_abs] using hmod i hi x hx)
    have hconst : IntervalIntegrable (fun _ : ℝ => g (a + (i : ℝ) * h)) volume
        (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h) := intervalIntegrable_const
    rw [intervalIntegral.integral_sub (hint i hi) hconst, intervalIntegral.integral_const] at hb
    have hwidth : a + ((i : ℝ) + 1) * h - (a + (i : ℝ) * h) = h := by ring
    simpa only [Real.norm_eq_abs, hwidth, smul_eq_mul, abs_of_nonneg hh,
      abs_sub_comm, pow_two, mul_assoc] using hb
  have hintSum : (∫ x in a..a + (n : ℝ) * h, g x) =
      ∑ i ∈ Finset.range n,
        ∫ x in (a + (i : ℝ) * h)..(a + ((i : ℝ) + 1) * h), g x := by
    simpa only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (a := fun i : ℕ => a + (i : ℝ) * h) (f := g) (n := n)
        (fun i hi => by simpa only [Nat.cast_add, Nat.cast_one] using hint i hi)).symm
  rw [hintSum, rectangleSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |h * g (a + (i : ℝ) * h) -
          ∫ x in (a + (i : ℝ) * h)..(a + ((i : ℝ) + 1) * h), g x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range n, K * h ^ 2 := Finset.sum_le_sum (fun i hi => hcell i (Finset.mem_range.mp hi))
    _ = _ := by simp; ring

theorem rectangleRule_numeric_error (g : ℝ → ℝ) (v : ℕ → ℝ) (a h K d : ℝ) (n : ℕ)
    (hh : 0 ≤ h)
    (hint : ∀ i < n, IntervalIntegrable g volume (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h))
    (hmod : ∀ i < n, ∀ x ∈ Set.Ioc (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h),
      |g x - g (a + (i : ℝ) * h)| ≤ K * h)
    (hvalue : ∀ i < n, |v i - g (a + (i : ℝ) * h)| ≤ d) :
    |h * (∑ i ∈ Finset.range n, v i) - ∫ x in a..a + (n : ℝ) * h, g x| ≤
      (n : ℝ) * (K * h ^ 2 + h * d) := by
  have hv : |h * (∑ i ∈ Finset.range n, v i) - rectangleSum g a h n| ≤ h * (n : ℝ) * d := by
    rw [rectangleSum, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hh]
    have hs : |∑ i ∈ Finset.range n, (v i - g (a + (i : ℝ) * h))| ≤ (n : ℝ) * d := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i hi => hvalue i (Finset.mem_range.mp hi))
    nlinarith
  have ht := rectangleRule_error g a h K n hh hint hmod
  have he := abs_sub_le (h * ∑ i ∈ Finset.range n, v i) (rectangleSum g a h n)
    (∫ x in a..a + (n : ℝ) * h, g x)
  nlinarith

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open MeasureTheory ProbabilityTheory









end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace CritWinSpin.Implementation.GaussianGrid





















theorem grid_nodes {R h : ℝ} {n i : ℕ} (hh : 0 ≤ h) (hn : (n : ℝ) * h = 2 * R) (hi : i < n) :
    -R ≤ -R + (i : ℝ) * h ∧ -R + ((i : ℝ) + 1) * h ≤ R := by
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hi1 : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hi
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right hi1 hh]









end CritWinSpin.Implementation.GaussianGrid

end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic







def gaussianCoinBudget (k : ℕ) : ℕ :=
  gaussianBits k + gaussianGridSize k + 2 * (gaussianMeshDen k) ^ 3 + 2






































theorem gaussianMeshDen_positive (k : ℕ) : 0 < gaussianMeshDen k := by
  dsimp [gaussianMeshDen]
  positivity

theorem gaussianMesh_positive (k : ℕ) : 0 < gaussianMesh k := by
  dsimp [gaussianMesh]
  have := gaussianMeshDen_positive k
  positivity



theorem gaussian_grid_interval (k : ℕ) :
    (gaussianGridSize k : ℝ) * (gaussianMesh k : ℝ) = 2 * (gaussianRadius k : ℝ) := by
  simp [gaussianGridSize, gaussianMesh, (Nat.ne_of_gt (gaussianMeshDen_positive k))]









end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic IsingLTL.BeliefProp









theorem take_ofFn_prefix (L R : ℕ) (ω : Fin (L + R) → Bool) :
    (List.ofFn ω).take L = List.ofFn (fun i => ω (Fin.castAdd R i)) := by
  rw [← Fin.ofFn_take_eq_take_ofFn (Nat.le_add_right L R)]
  rfl





end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CritWinSpin.Implementation.GaussianGridLaw

open GaussianGrid





















end CritWinSpin.Implementation.GaussianGridLaw

end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary IsingLTL.BeliefProp ProbabilityTheory MeasureTheory
open CritWinSpin.Implementation.GaussianGrid









theorem gaussianNode_bound (k : ℕ) (i : Fin (gaussianGridSize k)) :
    |(gaussianNode (k, i.val) : ℝ)| ≤ (gaussianRadius k : ℝ) := by
  have hh := grid_nodes (show 0 ≤ (gaussianMesh k : ℝ) from
    (by exact_mod_cast (gaussianMesh_positive k).le)) (gaussian_grid_interval k) i.isLt
  have he : (gaussianNode (k, i.val) : ℝ) =
      -(gaussianRadius k : ℝ) + (i.val : ℝ) * (gaussianMesh k : ℝ) := by
    simp [gaussianNode]
  rw [he]
  apply abs_le.mpr
  refine ⟨hh.1, ?_⟩
  have hd : 0 ≤ (gaussianMesh k : ℝ) := by exact_mod_cast (gaussianMesh_positive k).le
  linarith [hh.2]





end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled







end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open MeasureTheory
noncomputable section













end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory ProbabilityTheory






theorem gaussianNoiseBits_budget (k : ℕ) : gaussianNoiseBits k = gaussianCoinBudget k := by
  unfold gaussianNoiseBits gaussianNoiseTail gaussianCoinBudget
  omega







end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic









theorem bitBlock_ofFn {N B : ℕ} (ω : Fin (N * B) → Bool) (i : Fin N) :
    bitBlock ((List.ofFn ω, B), i.val) = List.ofFn (fun j => ω (blockIndex i j)) := by
  apply List.ext_getElem
  · simp only [bitBlock, List.length_take, List.length_drop, List.length_ofFn]
    have hm : i.val * B + B ≤ N * B := by
      nlinarith [Nat.mul_le_mul_right B (Nat.succ_le_of_lt i.isLt)]
    omega
  · intro j hj hj'
    simp only [bitBlock, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    congr 1

def splitBitEquiv (N B : ℕ) : (Fin (N * B) → Bool) ≃ (Fin N → Fin B → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin N) (Fin B) Bool)

theorem splitBitEquiv_apply (N B : ℕ) (ω : Fin (N * B) → Bool) (i : Fin N) (j : Fin B) :
    splitBitEquiv N B ω i j = ω (blockIndex i j) := by
  change ω (finProdFinEquiv (i, j)) = ω (blockIndex i j)
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv, blockIndex, Nat.mul_comm, Nat.add_comm]



end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic





theorem clampTwo_eq (x : ℚ) (hx : |x| ≤ 2) : clampTwo x = x := by
  obtain ⟨hl, hr⟩ := abs_le.mp hx
  simp [clampTwo, show ¬2 < x by linarith, show ¬x < -2 by linarith]

theorem roundTowardZero_scale (x d M : ℚ) (hM : 0 < M) :
    roundTowardZero (x / M, d / M) = roundTowardZero (x, d) / M := by
  have hx : x / M < 0 ↔ x < 0 := by simpa only [zero_mul] using (div_lt_iff₀ hM : x / M < 0 ↔ x < 0 * M)
  by_cases h : x < 0
  · simp only [roundTowardZero, hx, h, ite_true, neg_div]
    rw [div_div_div_cancel_right₀ hM.ne' x d]
    ring
  · simp only [roundTowardZero, hx, h, ite_false]
    rw [div_div_div_cancel_right₀ hM.ne' x d]
    ring

theorem boundedRound_eq (x d M : ℚ) (hM : 0 < M)
    (hx : |roundTowardZero (x, d)| ≤ 2 * M) :
    boundedRound ((x, d), M) = roundTowardZero (x, d) := by
  unfold boundedRound clampedRound
  rw [roundTowardZero_scale x d M hM]
  have hb : |roundTowardZero (x, d) / M| ≤ 2 := by
    rw [abs_div, abs_of_pos hM, div_le_iff₀ hM]
    exact hx
  rw [clampTwo_eq _ hb]
  field_simp





end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section





















































end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled

theorem gaussianDraw_bound (k : ℕ) (bits : List Bool) :
    |(gaussianDraw (k, bits) : ℝ)| ≤ (gaussianRadius k : ℝ) := by
  let nodes := gaussianNodes (k, bits)
  let ticket := bucketScan (gaussianCounts (k, bits), OAI.MetricKMedian.Binary.Word.value
    (bits.take (gaussianBits k)))
  change |((nodes[ticket]?).getD 0 : ℝ)| ≤ _
  cases hg : nodes[ticket]? with
  | none => simp only [hg, Option.getD_none, Rat.cast_zero, abs_zero]; positivity
  | some x =>
      simp only [hg, Option.getD_some]
      have hm : x ∈ nodes := List.mem_of_getElem? hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
      have hin : i < gaussianGridSize k := by
        have hrange := List.mem_range.mp hi
        change i < (bits.take (gaussianGridSize k)).length at hrange
        have hl := List.length_take_le (gaussianGridSize k) bits
        exact hrange.trans_le hl
      exact gaussianNode_bound k ⟨i, hin⟩

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open CritWinSpin.Implementation.EnvelopeAnalysis

theorem deriv_phis_abs_le_one (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t : ℝ) : |deriv (phis S s) t| ≤ 1 := by
  have hpos (u : ℝ) (hu : 0 ≤ u) : |deriv (phis S s) u| ≤ 1 := by
    rw [deriv_phis_min_nonneg S hS hs u hu]
    have hs0 := (tau_pos S).trans hs
    have ht : 0 ≤ u / s := div_nonneg hu hs0.le
    obtain ⟨hl, hr⟩ := abs_le.mp (deriv_phi_bdd S u)
    apply abs_le.mpr
    exact ⟨le_min (by linarith) hl, (min_le_right _ _).trans hr⟩
  by_cases ht : 0 ≤ t
  · exact hpos t ht
  · have hh := hpos (-t) (by linarith)
    rwa [deriv_phis_neg S hS hs, abs_neg] at hh

theorem modifiedDerivativeApprox_bound (S : SpinLaw) (hS : IsGHS S) (s t d : ℚ)
    (hs : tau S < (s : ℝ)) (hd : 0 < d) (hd1 : d ≤ 1) :
    |(modifiedDerivativeApprox S s t d : ℝ)| ≤
      1 + 2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ) := by
  have he := modifiedDerivativeApprox_error S hS s t d hs hd hd1
  have hb := deriv_phis_abs_le_one S hS hs (t : ℝ)
  have ht := abs_add_le
    ((modifiedDerivativeApprox S s t d : ℝ) - deriv (phis S s) (t : ℝ))
    (deriv (phis S s) (t : ℝ))
  rw [sub_add_cancel] at ht
  linarith

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section











theorem bitBlock_append (xs ys : List Bool) (B i : ℕ) (hi : (i + 1) * B ≤ xs.length) :
    bitBlock ((xs ++ ys, B), i) = bitBlock ((xs, B), i) := by
  have hi0 : i * B ≤ xs.length := by nlinarith
  have hi1 : i * B + B ≤ xs.length := by nlinarith
  unfold bitBlock
  rw [List.drop_append]
  have hz : i * B - xs.length = 0 := Nat.sub_eq_zero_of_le hi0
  rw [hz, List.drop_zero]
  apply List.take_append_of_le_length
  simp only [List.length_drop]
  omega

theorem eulerDrift_ofFn {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ) ^ 3 + 2 ≤ D.fuel.length)
    (z : Fin N → ℚ) (bits : List Bool) :
    eulerDrift S (D.context, (List.ofFn z, bits)) =
      List.ofFn (approximateGradient S D.L D.h (fun i => roundTowardZero (z i, D.snap))
        D.sCap D.a D.dPhi) := by
  change snappedDriftWithFuel S (D.snap, driftInputOf D.L D.h z D.sCap D.a D.dPhi D.fuel) = _
  exact snappedDriftWithFuel_correct S D.L D.h z D.sCap D.a D.dPhi D.snap hd D.fuel hf

theorem eulerNoise_ofFn {N : ℕ} (D : EulerData N) (z : Fin N → ℚ)
    (ω : Fin (N * gaussianNoiseBits D.k) → Bool) (tail : List Bool) (i : Fin N) :
    eulerNoise ((D.context, (List.ofFn z, List.ofFn ω ++ tail)), i.val) =
      gaussianDraw (D.k, List.ofFn (fun j => ω (blockIndex i j))) := by
  change gaussianDraw (D.k,
    bitBlock ((List.ofFn ω ++ tail, gaussianNoiseBits D.k), i.val)) = _
  have hi : (i.val + 1) * gaussianNoiseBits D.k ≤ (List.ofFn ω).length := by
    simp only [List.length_ofFn]
    exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt)
  rw [bitBlock_append _ _ _ _ hi, bitBlock_ofFn]

theorem eulerRaw_ofFn {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ) ^ 3 + 2 ≤ D.fuel.length)
    (z : Fin N → ℚ) (ω : Fin (N * gaussianNoiseBits D.k) → Bool)
    (tail : List Bool) (i : Fin N) :
    eulerRaw S ((D.context, (List.ofFn z, List.ofFn ω ++ tail)), i.val) = D.raw S z ω i := by
  change ((List.ofFn z)[i.val]?).getD 0 - D.sigma * D.sigma *
    ((eulerDrift S (D.context, (List.ofFn z, List.ofFn ω ++ tail)))[i.val]?).getD 0 +
      D.sigma * eulerNoise ((D.context, (List.ofFn z, List.ofFn ω ++ tail)), i.val) = _
  rw [eulerDrift_ofFn S D hd hf, eulerNoise_ofFn]
  simp only [List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some, EulerData.raw, pow_two]

theorem eulerRows_ofFn {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ) ^ 3 + 2 ≤ D.fuel.length)
    (z : Fin N → ℚ) (ω : Fin (N * gaussianNoiseBits D.k) → Bool) (tail : List Bool) :
    eulerRows S (D.context, (List.ofFn z, List.ofFn ω ++ tail)) = List.ofFn (D.cappedNext S z ω) := by
  unfold eulerRows
  have hn : siteNumbers D.context.1.2.1 = List.range N := by simp [EulerData.context, siteNumbers]
  rw [hn]
  change (List.range N).map (fun i => boundedRound
    ((eulerRaw S ((D.context, (List.ofFn z, List.ofFn ω ++ tail)), i), D.dRound), D.bound)) = _
  rw [map_range_eq_ofFn]
  congr 1
  funext i
  rw [eulerRaw_ofFn S D hd hf]
  rfl

theorem eulerStep_ofFn {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ) ^ 3 + 2 ≤ D.fuel.length)
    (z : Fin N → ℚ) (ω : Fin (N * gaussianNoiseBits D.k) → Bool) (tail : List Bool) :
    eulerStep S (D.context, (List.ofFn z, List.ofFn ω ++ tail)) =
      (D.context, (List.ofFn (D.cappedNext S z ω), tail)) := by
  unfold eulerStep
  rw [eulerRows_ofFn S D hd hf]
  have hn : D.context.1.2.1.length = N := by simp [EulerData.context]
  simp only [hn]
  change (D.context, (List.ofFn (D.cappedNext S z ω),
    (List.ofFn ω ++ tail).drop (N * gaussianNoiseBits D.k))) = _
  simp

theorem EulerData.cappedNext_eq_next {N : ℕ} (D : EulerData N) (S : SpinLaw)
    (hB : 0 < D.bound) (z : Fin N → ℚ) (ω : Fin (N * gaussianNoiseBits D.k) → Bool)
    (hsmall : ∀ i, |D.next S z ω i| ≤ 2 * D.bound) : D.cappedNext S z ω = D.next S z ω := by
  funext i
  exact boundedRound_eq _ _ _ hB (hsmall i)

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
noncomputable section









end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
open CritWinSpin.Implementation.EnvelopeGeometry
noncomputable section





















end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
noncomputable section







end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace CritWinSpin.Implementation.ProductWeak

def prepend {n : ℕ} (u : ℝ) (z : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons u z
@[simp] theorem prepend_zero {n : ℕ} (u : ℝ) (z : Fin n → ℝ) : prepend u z 0 = u := rfl
@[simp] theorem prepend_succ {n : ℕ} (u : ℝ) (z : Fin n → ℝ) (i : Fin n) : prepend u z i.succ = z i := rfl





















end CritWinSpin.Implementation.ProductWeak

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.RoundedEuler

open ContractiveOperator NoiseOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]











def eulerDrift (g : E → E) (s : ℝ) (x : E) : E := x - s ^ 2 • g x







end CritWinSpin.Implementation.RoundedEuler
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CritWinSpin.Implementation.EulerNoiseOperator
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open EnvelopeGeometry ContractiveOperator

def noiseLaw {N : ℕ} (D : EulerData N) : Measure (Point N) :=
  (Measure.pi (fun _ : Fin N => gaussianNoiseLaw D.k)).map (WithLp.toLp 2)

instance noiseLaw_probability {N : ℕ} (D : EulerData N) : IsProbabilityMeasure (noiseLaw D) :=
  Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 (Fin N → ℝ)).aemeasurable











end CritWinSpin.Implementation.EulerNoiseOperator
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace CritWinSpin.Implementation.EulerAnalyticStep
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open EnvelopeGeometry ContractiveOperator LangevinBudget EulerNoiseOperator

def driftError {N : ℕ} (S : SpinLaw) (D : EulerData N) (entryBound : ℝ) : ℝ :=
  ((N:ℝ)+1)*((N:ℝ)*entryBound*
    (2*(Fintype.card {x : ℚ // x ∈ S.A}:ℝ)*(D.dPhi:ℝ)/(S.ρ 1:ℝ))+2*(D.snap:ℝ))

def stepError {N : ℕ} (S : SpinLaw) (D : EulerData N) (entryBound : ℝ) : ℝ :=
  (D.sigma:ℝ)^2*driftError S D entryBound + (D.sigma:ℝ)*((N:ℝ)/((D.k:ℝ)+1)) +
    ((N:ℝ)+1)*(D.dRound:ℝ)





theorem trajectory_weak {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (D : EulerData N)
    (hs : tau S < (D.sCap:ℝ)) (ha : 0 < D.a) (ha1 : D.a ≤ 1)
    (hPSD : ((D.sCap:ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM D.L*(castM D.L).transpose).PosSemidef)
    (hd : 0 < D.dPhi) (hd1 : D.dPhi ≤ 1) (hsnap : 0 < D.snap)
    (hr : 0 < D.dRound) (hsigma : 0 < D.sigma) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ i j, |(D.L i j:ℝ)| ≤ B)
    (cert : Certificate N (D.a:ℝ))
    (hUeq : cert.U = potential S D.sCap D.a (castM D.L) (castV D.h))
    (hGeq : cert.g = gradient S D.sCap D.a (castM D.L) (castV D.h))
    {R : ℝ} (hR : 2 ≤ R) (haR : 1 ≤ (D.a:ℝ)*R)
    (hsR : (D.sigma:ℝ) ≤ 1/(2048*R^4))
    (hError : stepError S D B ≤ (D.sigma:ℝ)^2/(16*R^3))
    (hM : (∫ x, ‖x‖ ∂DensityAnalysis.gibbs cert.U) ≤ R)
    (hH : 2+(∫ x, ‖cert.g x‖^6 ∂DensityAnalysis.gibbs cert.U)+
      GaussianMoments.sixthConstant*(N:ℝ)^3 ≤ R)
    (T : ℕ) (hT : 16*R^4/(D.sigma:ℝ)^2 ≤ (T:ℝ))
    (f : Point N → ℝ) (Bf L : ℝ) (hLip : 0 ≤ L) (hLR : L ≤ R) (hf : BoundedLip f Bf L) :
    |(∫ x, f x ∂D.trajectoryLaw S T (0 : Fin N → ℚ))-
      ∫ x, f x ∂DensityAnalysis.gibbs (potential S D.sCap D.a (castM D.L) (castV D.h))| ≤ 1/(2*R) := by
  have he :
      (D.sigma:ℝ)^2 * (((N:ℝ)+1)*((N:ℝ)*B*
        (2*(Fintype.card {x:ℚ // x∈S.A}:ℝ)*(D.dPhi:ℝ)/(S.ρ 1:ℝ))+2*(D.snap:ℝ))) +
        (D.sigma:ℝ)*((N:ℝ)/((D.k:ℝ)+1))+((N:ℝ)+1)*(D.dRound:ℝ) ≤
      (D.sigma:ℝ)^2/(16*R^3) := by
    simpa only [EulerAnalyticStep.stepError,EulerAnalyticStep.driftError] using hError
  exact CritWinSpin.rounded_euler_weak_budget S hS D hs ha ha1 hPSD hd hd1 hsnap hr hsigma B hB hL
    cert hUeq hGeq hR haR hsR he hM hH T hT f Bf L hLip hLR hf.1 hf.2.1 hf.2.2

end CritWinSpin.Implementation.EulerAnalyticStep
end

end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.EulerPrecisionArithmetic

theorem error_budget {R N B K : ℝ} (hR : 2 ≤ R) (hN0 : 0 ≤ N) (hN : N+1 ≤ R)
    (hB0 : 0 ≤ B) (hB : B ≤ R) (hK0 : 0 ≤ K) (hK : K ≤ R) :
    let d := 1/R^100
    let s := 1/(2048*R^4)
    s^2*((N+1)*(N*B*(K*d)+2*d)) + s*(N/(R^100+1)) + (N+1)*d ≤ s^2/(16*R^3) := by
  let d : ℝ := 1/R^100
  let s : ℝ := 1/(2048*R^4)
  have hRp : 0 < R := by linarith only [hR]
  have hR0 : 0 ≤ R := hRp.le
  have hR1 : 1 ≤ R := by linarith only [hR]
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by
    dsimp [s]
    apply (div_le_one (by positivity : 0 < 2048*R^4)).2
    have hh : 1 ≤ R^4 := one_le_pow₀ hR1
    nlinarith only [hh]
  have hs2 : s^2 ≤ 1 := by nlinarith only [hs0,hs1]
  have hNR : N ≤ R := by linarith only [hN]
  have hNB : N*B ≤ R^2 := by
    have hh := mul_le_mul hNR hB hB0 hR0
    nlinarith only [hh]
  have hNBK : N*B*K ≤ R^3 := by
    have hh := mul_le_mul hNB hK hK0 (sq_nonneg R)
    nlinarith only [hh]
  have hR3 : 2 ≤ R^3 := by
    have hh : R ≤ R^3 := by simpa only [pow_one] using pow_le_pow_right₀ hR1 (show 1 ≤ (3:ℕ) by decide)
    linarith only [hh,hR]
  have hG0 : 0 ≤ (N+1)*(N*B*(K*d)+2*d) := by positivity
  have hG : (N+1)*(N*B*(K*d)+2*d) ≤ 2*R^4*d := by
    have hi : N*B*(K*d)+2*d ≤ R^3*d+2*d := by
      have hh := mul_le_mul_of_nonneg_right hNBK hd
      nlinarith only [hh]
    have ht := mul_le_mul hN hi (by positivity : 0 ≤ N*B*(K*d)+2*d) hR0
    have hg := mul_nonneg (show 0 ≤ R^3-2 by linarith only [hR3]) (mul_nonneg hR0 hd)
    nlinarith only [ht,hg]
  have hNoise : N/(R^100+1) ≤ R*d := by
    dsimp [d]
    rw [mul_one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < R^100+1) (by positivity : 0 < R^100)).2
    have hh := mul_le_mul_of_nonneg_right hNR (pow_nonneg hR0 100)
    nlinarith only [hh,hR0]
  have hRound := mul_le_mul_of_nonneg_right hN hd
  have hSGrad := mul_le_of_le_one_left hG0 hs2
  have hSNoise := mul_le_of_le_one_left (show 0 ≤ N/(R^100+1) by positivity) hs1
  have hR4 : R ≤ R^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hR1 (show 1 ≤ (4:ℕ) by decide)
  have hPow := mul_le_mul_of_nonneg_right hR4 hd
  have hTotal : s^2*((N+1)*(N*B*(K*d)+2*d))+s*(N/(R^100+1))+(N+1)*d ≤ 4*R^4*d := by
    nlinarith only [hG,hNoise,hRound,hSGrad,hSNoise,hPow]
  have h85 : (268435456:ℝ) ≤ R^85 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hR 85
    exact (by norm_num : (268435456:ℝ) ≤ (2:ℝ)^85).trans hh
  have hSmall : 4*R^4*d ≤ 1/(67108864*R^11) := by
    dsimp [d]
    rw [mul_one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < R^100) (by positivity : 0 < 67108864*R^11)).2
    have hh := mul_le_mul_of_nonneg_left h85 (pow_nonneg hR0 15)
    nlinarith only [hh]
  have hTarget : s^2/(16*R^3) = 1/(67108864*R^11) := by
    dsimp [s]
    field_simp [hRp.ne'] <;> ring
  change s^2*((N+1)*(N*B*(K*d)+2*d))+s*(N/(R^100+1))+(N+1)*d ≤ s^2/(16*R^3)
  rw [hTarget]
  exact hTotal.trans hSmall

theorem stepCount_formula {R : ℝ} (hR : 0 < R) :
    16*R^4/(1/(2048*R^4))^2 = 16*2048^2*R^12 := by
  field_simp [hR.ne'] <;> ring

end CritWinSpin.Implementation.EulerPrecisionArithmetic
end

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

open Matrix






































end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2











end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

open Matrix

namespace CritWinSpin.LocalTM2







theorem coordinate_product_bound {N : ℕ} (x : Fin N → ℝ) (i j : Fin N) :
    |x i * x j| ≤ ∑ k, (x k) ^ 2 := by
  have hi : (x i) ^ 2 ≤ ∑ k, (x k) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ i)
  have hj : (x j) ^ 2 ≤ ∑ k, (x k) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ j)
  have h := sq_nonneg (|x i| - |x j|)
  rw [abs_mul]
  nlinarith [sq_abs (x i), sq_abs (x j)]









end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix

theorem roundedMatrixSqrt_symm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : A.IsSymm) (d : ℚ) (n : ℕ) : (roundedMatrixSqrt A d n).IsSymm := by
  induction n with
  | zero => exact Matrix.isSymm_zero
  | succ n ih =>
      have hs : (sqrtStepQ A (roundedMatrixSqrt A d n)).IsSymm :=
        ih.add ((hA.sub (ih.pow 2)).smul (1 / 2 : ℚ))
      apply Matrix.IsSymm.ext
      intro i j
      change Compiled.clampedRound ((sqrtStepQ A (roundedMatrixSqrt A d n)) j i, d) =
        Compiled.clampedRound ((sqrtStepQ A (roundedMatrixSqrt A d n)) i j, d)
      rw [hs.apply i j]

theorem quadratic_absolute_entry_bound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (e : ℝ) (he : 0 ≤ e) (hA : ∀ i j, |A i j| ≤ e) (x : Fin N → ℝ) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ (N : ℝ) ^ 2 * e * (∑ k, (x k) ^ 2) := by
  have heq : x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, A i j * (x i * x j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i, |∑ j, A i j * (x i * x j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * (x i * x j)| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, e * (∑ k, (x k) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hA i j) (coordinate_product_bound x i j) (abs_nonneg _) he
    _ = _ := by simp; ring

theorem positive_up_to_entry_error {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (e : ℝ) (he : 0 ≤ e) (hE : ∀ i j, |A i j| ≤ e) :
    (A + ((N : ℝ) ^ 2 * e) • (1 : Matrix (Fin N) (Fin N) ℝ)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact hA.add (Matrix.isHermitian_one.smul (by rfl))
  · intro x
    have hh := (abs_le.mp (quadratic_absolute_entry_bound A e he hE x)).1
    have hs : star x = x := by ext i; simp
    rw [hs]
    have hq : x ⬝ᵥ ((A + ((N : ℝ) ^ 2 * e) • (1 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ x) =
        x ⬝ᵥ (A *ᵥ x) + (N : ℝ) ^ 2 * e * (∑ k, (x k) ^ 2) := by
      simp [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct, Finset.sum_add_distrib,
        pow_two, Finset.mul_sum, mul_left_comm, mul_add]
    rw [hq]
    linarith

theorem approximate_square_root_psd {N : ℕ} (A Y : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (hY : Y.IsHermitian) (e : ℝ) (he : 0 ≤ e)
    (hres : ∀ i j, |(A - Y ^ 2) i j| ≤ e) :
    (A + ((N : ℝ) ^ 2 * e) • (1 : Matrix (Fin N) (Fin N) ℝ)).PosSemidef := by
  have hr := positive_up_to_entry_error (A - Y ^ 2) (hA.sub (hY.pow 2)) e he hres
  have hy : (Y ^ 2).PosSemidef := by
    simpa only [hY.eq, pow_two] using Matrix.posSemidef_conjTranspose_mul_self Y
  have hh := hy.add hr
  convert hh using 1
  abel

theorem psd_scalar_entry_bound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hA : A.PosSemidef)
    (hAc : (c • (1 : Matrix (Fin N) (Fin N) ℝ) - A).PosSemidef)
    (i j : Fin N) : |A i j| ≤ c := by
  have hi0 := hA.diag_nonneg (i := i)
  have hj0 := hA.diag_nonneg (i := j)
  have hi : A i i ≤ c := by
    have hh := hAc.diag_nonneg (i := i)
    simpa using hh
  have hj : A j j ≤ c := by
    have hh := hAc.diag_nonneg (i := j)
    simpa using hh
  have hd : 0 ≤ A i i * A j j - A i j * A j i := by
    have hh := (hA.submatrix (![i, j] : Fin 2 → Fin N)).det_nonneg
    rw [Matrix.det_fin_two] at hh
    simpa using hh
  rw [(Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).apply i j] at hd
  have hp := mul_le_mul hi hj hj0 hc
  nlinarith [sq_abs (A i j), abs_nonneg (A i j)]

theorem roundedMatrixSqrt_residual {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : (castM A).PosSemidef)
    (hA1 : ((1 : Matrix (Fin N) (Fin N) ℝ) - castM A).PosSemidef)
    (d : ℚ) (hd : 0 < d) (n : ℕ) (i j : Fin N) :
    |(castM A - (castM (roundedMatrixSqrt A d n)) ^ 2) i j| ≤
      4 / ((n : ℝ) + 2) +
        4 * (N : ℝ) * ((d : ℝ) * n * (1 + 2 * (N : ℝ)) ^ n) := by
  let X := matrixSqrtIter (castM A) n
  let Y := castM (roundedMatrixSqrt A d n)
  let e : ℝ := (d : ℝ) * n * (1 + 2 * (N : ℝ)) ^ n
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : 0 ≤ e := by dsimp [e]; positivity
  obtain ⟨_, _, hr, hr1⟩ := matrixSqrtIter_certificates (castM A) hA hA1 n
  have hib := psd_scalar_entry_bound _ (4 / ((n : ℝ) + 2)) (by positivity) hr hr1 i j
  have hs := matrix_square_entry_difference Y X 2 e (by norm_num) he
    (roundedMatrixSqrt_entry_bound A d n)
    (fun i j => (matrixSqrtIter_entry_bound _ hA hA1 n i j).trans (by norm_num))
    (roundedMatrixSqrt_error A hA hA1 d hd n) i j
  have hid : (castM A - Y ^ 2) i j = (castM A - X ^ 2) i j - (Y ^ 2 - X ^ 2) i j := by
    simp only [Matrix.sub_apply]
    ring
  rw [hid]
  have hh := (abs_sub_le ((castM A - X ^ 2) i j) 0 ((Y ^ 2 - X ^ 2) i j))
  simp only [sub_zero, zero_sub, abs_neg] at hh
  exact hh.trans ((add_le_add hib hs).trans_eq (by dsimp [e]; ring))

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic











theorem rootResidualTest_correct {N : ℕ} (A Y : Matrix (Fin N) (Fin N) ℚ)
    (e : ℚ) :
    rootResidualTest ((List.ofFn (fun i => List.ofFn (A i)),
      List.ofFn (fun i => List.ofFn (Y i))), (List.replicate N (), e)) = true ↔
      ∀ i j, |(A - Y ^ 2) i j| ≤ e := by
  simp only [rootResidualTest, siteNumbers, List.length_replicate, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  constructor
  · intro h i j
    have hh := h i.val i.isLt j.val j.isLt
    simpa only [matrixEntry_ofFn, matrixProductEntry_ofFn Y _ (List.length_replicate ..),
      Matrix.sub_apply] using hh
  · intro h i hi j hj
    rw [matrixEntry_ofFn A ⟨i, hi⟩ ⟨j, hj⟩,
      matrixProductEntry_ofFn Y _ (List.length_replicate ..) ⟨i, hi⟩ ⟨j, hj⟩]
    exact h ⟨i, hi⟩ ⟨j, hj⟩











theorem rootTolerance_formula (sites fuel : List Unit) (e : ℚ) :
    rootTolerance ((sites, fuel), e) =
      e / (8 * ((sites.length : ℚ) + 1) * ((fuel.length : ℚ) + 1) *
        (1 + 2 * (sites.length : ℚ)) ^ fuel.length) := by
  have hp : (fuel.map (fun _ => 1 + 2 * sites.length)).prod =
      (1 + 2 * sites.length) ^ fuel.length := by
    induction fuel with
    | nil => simp
    | cons a fuel ih => simp [ih, pow_succ, mul_comm]
  simp only [rootTolerance, naturalProduct_eq, hp, Nat.cast_pow, Nat.cast_add,
    Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]



end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeIntegral

open EnvelopeAnalysis

theorem phi_second_derivative_le_one (S : SpinLaw) (t : ℝ) : deriv (deriv (phi S)) t ≤ 1 := by
  have hsum : (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) ≤ mgf S t := by
    unfold mgf
    apply Finset.sum_le_sum
    intro x hx
    have hxq := S.mem_Icc x hx
    have hxR : -1 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1 := by exact_mod_cast hxq
    have hx2 : (x : ℝ) ^ 2 ≤ 1 := by nlinarith [hxR.1, hxR.2]
    have hρ : 0 ≤ (S.ρ x : ℝ) := by exact_mod_cast (S.pos x hx).le
    have hh := mul_le_mul_of_nonneg_right hx2 (mul_nonneg hρ (Real.exp_pos (t * (x : ℝ))).le)
    nlinarith only [hh]
  rw [(hasDerivAt_deriv_phi S t).deriv, div_le_one (sq_pos_of_pos (mgf_pos S t))]
  have hh := mul_le_mul_of_nonneg_right hsum (mgf_pos S t).le
  nlinarith [sq_nonneg (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ)))]

theorem phiDerivative_lipschitz (S : SpinLaw) : LipschitzWith 1 (deriv (phi S)) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hasDerivAt_deriv_phi S t).differentiableAt)
  intro t
  have hlo : 0 ≤ deriv (deriv (phi S)) t := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using deriv2_phi_nonneg S t
  have hh : |deriv (deriv (phi S)) t| ≤ 1 := by
    rw [abs_of_nonneg hlo]
    exact phi_second_derivative_le_one S t
  exact_mod_cast hh

def integrand (S : SpinLaw) (s u : ℝ) : ℝ := max (deriv (phi S) u - u / s) 0

theorem integrand_continuous (S : SpinLaw) (s : ℝ) : Continuous (integrand S s) :=
  ((phiDerivative_lipschitz S).continuous.sub (continuous_id.div_const s)).max continuous_const

theorem integrand_nonneg (S : SpinLaw) (s u : ℝ) : 0 ≤ integrand S s u := le_max_right _ _



theorem integrand_modulus (S : SpinLaw) {s : ℝ} (hs : 0 < s) (x y : ℝ) :
    |integrand S s x - integrand S s y| ≤ (1 + 1 / s) * |x - y| := by
  have hφ : |deriv (phi S) x - deriv (phi S) y| ≤ |x - y| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using (phiDerivative_lipschitz S).dist_le_mul x y
  calc
    _ ≤ |(deriv (phi S) x - x / s) - (deriv (phi S) y - y / s)| :=
      abs_max_sub_max_le_abs _ _ 0
    _ = |(deriv (phi S) x - deriv (phi S) y) - (x - y) / s| := by congr 1; ring
    _ ≤ |deriv (phi S) x - deriv (phi S) y| + |(x - y) / s| := abs_sub _ _
    _ ≤ |x - y| + |x - y| / s := by rw [abs_div, abs_of_pos hs]; linarith
    _ = _ := by ring

theorem discrepancy_eq (S : SpinLaw) (s t : ℝ) : ds S s t = phis S s t - phi S t := by
  unfold ds phis fs
  ring

theorem asOf_le_s (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) : asOf S s ≤ s := by
  obtain ⟨a, ha, heq, _, _, hasOf⟩ := asOf_props_direct S hS hs
  have hφ := (abs_le.mp (deriv_phi_bdd S a)).2
  have hs0 := (tau_pos S).trans hs
  rw [hasOf]
  nlinarith

theorem discrepancy_outside (S : SpinLaw) (s t : ℝ) (ht : asOf S s ≤ |t|) : ds S s t = 0 := by
  have habs : fs S s |t| = fs S s t := by
    by_cases ht0 : 0 ≤ t
    · rw [abs_of_nonneg ht0]
    · rw [abs_of_neg (lt_of_not_ge ht0), fs_even]
  by_cases hinside : |t| ≤ asOf S s
  · have heq := le_antisymm hinside ht
    have hf : fs S s t = fs S s (asOf S s) := by rw [← habs, heq]
    unfold ds gs
    rw [if_pos hinside, hf, sub_self]
  · unfold ds gs
    rw [if_neg hinside, sub_self]

theorem discrepancy_abs (S : SpinLaw) (s t : ℝ) : ds S s |t| = ds S s t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), ds_even]

theorem discrepancy_clamp (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) (t : ℝ) :
    ds S s (min |t| s) = ds S s t := by
  have hs0 := (tau_pos S).trans hs
  by_cases ht : |t| ≤ s
  · rw [min_eq_left ht, discrepancy_abs]
  · have hst : s ≤ |t| := le_of_lt (lt_of_not_ge ht)
    rw [min_eq_right hst, discrepancy_outside S s s (by rw [abs_of_pos hs0]; exact asOf_le_s S hS hs),
      discrepancy_outside S s t ((asOf_le_s S hS hs).trans hst)]

theorem neg_discrepancy_derivative (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (u : ℝ) (hu : 0 ≤ u) : HasDerivAt (fun v => -ds S s v) (integrand S s u) u := by
  have hφ : HasDerivAt (phi S) (deriv (phi S) u) u :=
    ((phi_contDiff S).differentiable (by simp) u).hasDerivAt
  have hψ : HasDerivAt (phis S s) (deriv (phis S s) u) u :=
    (hasDerivAt_phis_direct S hS hs u).differentiableAt.hasDerivAt
  have hf : (fun v => -ds S s v) = fun v => -(phis S s v - phi S v) := by
    funext v
    rw [discrepancy_eq]
  rw [hf]
  refine ((hψ.sub hφ).neg).congr_deriv ?_
  rw [LocalTM2.deriv_phis_min_nonneg S hS hs u hu]
  unfold integrand
  by_cases hh : u / s ≤ deriv (phi S) u
  · rw [min_eq_left hh, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hh)), max_eq_right (by linarith)]
    ring

theorem discrepancy_integral (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) (t : ℝ) :
    phis S s t - phi S t = ∫ u in (min |t| s)..s, integrand S s u := by
  have hs0 := (tau_pos S).trans hs
  let r := min |t| s
  have hr0 : 0 ≤ r := le_min (abs_nonneg _) hs0.le
  have hrs : r ≤ s := min_le_right _ _
  have hd : ∀ u ∈ Set.uIcc r s, HasDerivAt (fun v => -ds S s v) (integrand S s u) u := by
    intro u hu
    rw [Set.uIcc_of_le hrs] at hu
    exact neg_discrepancy_derivative S hS hs u (hr0.trans hu.1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((integrand_continuous S s).intervalIntegrable r s)
  have hds_s : ds S s s = 0 := discrepancy_outside S s s (by rw [abs_of_pos hs0]; exact asOf_le_s S hS hs)
  rw [hds_s] at he
  have hds_r : ds S s r = ds S s t := discrepancy_clamp S hS hs t
  rw [hds_r] at he
  rw [← discrepancy_eq]
  change ds S s t = ∫ u in r..s, integrand S s u
  linarith

theorem discrepancy_le_at_zero (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) (t : ℝ) :
    ds S s t ≤ ds S s 0 := by
  have hs0 := (tau_pos S).trans hs
  have hrep (u : ℝ) : ds S s u = ∫ v in (min |u| s)..s, integrand S s v := by
    rw [discrepancy_eq]
    exact discrepancy_integral S hS hs u
  rw [hrep t, hrep 0, abs_zero, min_eq_left hs0.le]
  exact intervalIntegral.integral_mono_interval (c := 0) (a := min |t| s) (b := s) (d := s)
    (le_min (abs_nonneg _) hs0.le) (min_le_right _ _) le_rfl
    (Filter.Eventually.of_forall fun u => integrand_nonneg S s u)
    ((integrand_continuous S s).intervalIntegrable _ _)

end CritWinSpin.Implementation.EnvelopeIntegral

end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic MeasureTheory
open CritWinSpin.Implementation.EnvelopeIntegral
noncomputable section







theorem envelopeLeft_eq (s t : ℚ) : envelopeLeft (s, t) = min |t| s := by
  unfold envelopeLeft rationalMin
  rw [show (if t < 0 then -t else t) = |t| by
    by_cases ht : t < 0 <;> simp [ht, abs_of_neg, abs_of_nonneg, le_of_not_gt]]
  exact (min_def _ _).symm

















theorem envelopeValue_error (S : SpinLaw) (s t d : ℚ) (grid fuel : List Unit)
    (hd : 0 < d) (hd1 : d ≤ 1) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length)
    (i : ℕ) (hu : 0 ≤ envelopeNode ((((s, t, d), grid), fuel), i)) :
    |(envelopeValue S ((((s, t, d), grid), fuel), i) : ℝ) -
      integrand S s (envelopeNode ((((s, t, d), grid), fuel), i))| ≤
        2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ) := by
  let u := envelopeNode ((((s, t, d), grid), fuel), i)
  have he := phiDerivativeApprox_error S u d hu hd hd1
  have hmean := phiMeanWithFuel_correct S u d hu hd fuel hf
  have hv : (envelopeValue S ((((s, t, d), grid), fuel), i) : ℝ) =
      max ((phiDerivativeApprox S u d : ℝ) - (u : ℝ) / s) 0 := by
    change ((if 0 ≤ phiMeanWithFuel S ((u, d), fuel) - u / s then
      phiMeanWithFuel S ((u, d), fuel) - u / s else 0 : ℚ) : ℝ) = _
    rw [hmean]
    have hmax : (if 0 ≤ phiDerivativeApprox S u d - u / s then
        phiDerivativeApprox S u d - u / s else 0) = max (phiDerivativeApprox S u d - u / s) 0 := by
      rw [max_def]
      split_ifs <;> linarith
    rw [hmax]
    simp
  rw [hv]
  change |max ((phiDerivativeApprox S u d : ℝ) - (u : ℝ) / s) 0 -
    max (deriv (phi S) (u : ℝ) - (u : ℝ) / s) 0| ≤ _
  have hm := abs_max_sub_max_le_abs ((phiDerivativeApprox S u d : ℝ) - (u : ℝ) / s)
    (deriv (phi S) (u : ℝ) - (u : ℝ) / s) 0
  have heq : ((phiDerivativeApprox S u d : ℝ) - (u : ℝ) / s) -
      (deriv (phi S) (u : ℝ) - (u : ℝ) / s) =
      (phiDerivativeApprox S u d : ℝ) - deriv (phi S) (u : ℝ) := by ring
  rw [heq] at hm
  exact hm.trans he

theorem envelopeWithFuel_error (S : SpinLaw) (hS : IsGHS S) (s t d : ℚ)
    (hs : tau S < (s : ℝ)) (grid fuel : List Unit) (hn : 0 < grid.length)
    (hd : 0 < d) (hd1 : d ≤ 1) (hf : 2 / (d : ℝ) ^ 3 + 2 ≤ fuel.length) :
    |(envelopeWithFuel S (((s, t, d), grid), fuel) : ℝ) -
      (phis S s t - phi S t)| ≤
        (grid.length : ℝ) *
          ((1 + 1 / (s : ℝ)) * (envelopeMesh (((s, t, d), grid), fuel) : ℝ) ^ 2 +
            (envelopeMesh (((s, t, d), grid), fuel) : ℝ) *
              (2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ))) := by
  let u : EnvelopeInput := (((s, t, d), grid), fuel)
  let a : ℚ := envelopeLeft (s, t)
  let h : ℚ := envelopeMesh u
  have hs0 : (0 : ℝ) < s := (CritWinSpin.Implementation.EnvelopeAnalysis.tau_pos S).trans hs
  have hsQ : 0 < s := by exact_mod_cast hs0
  have ha : 0 ≤ a ∧ a ≤ s := by
    dsimp only [a]
    rw [envelopeLeft_eq]
    exact ⟨le_min (abs_nonneg _) hsQ.le, min_le_right _ _⟩
  have hh : 0 ≤ h := div_nonneg (sub_nonneg.mpr ha.2) (Nat.cast_nonneg _)
  have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
  have hnr : (grid.length : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hend : (a : ℝ) + (grid.length : ℝ) * h = s := by
    change (a : ℝ) + (grid.length : ℝ) * (((s - a) / (grid.length : ℚ) : ℚ) : ℝ) = s
    push_cast
    field_simp
    <;> ring
  have hleft : (a : ℝ) = min |(t : ℝ)| (s : ℝ) := by
    dsimp only [a]
    rw [envelopeLeft_eq]
    exact_mod_cast rfl
  have hcont := integrand_continuous S (s : ℝ)
  have hint : ∀ i < grid.length, IntervalIntegrable (integrand S s) volume
      ((a : ℝ) + i * h) ((a : ℝ) + ((i : ℝ) + 1) * h) :=
    fun _ _ => hcont.intervalIntegrable _ _
  have hmod : ∀ i < grid.length, ∀ x ∈ Set.Ioc ((a : ℝ) + i * h)
      ((a : ℝ) + ((i : ℝ) + 1) * h),
      |integrand S s x - integrand S s ((a : ℝ) + i * h)| ≤ (1 + 1 / (s : ℝ)) * h := by
    intro i hi x hx
    have ht := integrand_modulus S hs0 x ((a : ℝ) + i * h)
    have hx0 : 0 ≤ x - ((a : ℝ) + i * h) := by linarith [hx.1]
    rw [abs_of_nonneg hx0] at ht
    have hc : 0 ≤ 1 + 1 / (s : ℝ) := by positivity
    exact ht.trans (mul_le_mul_of_nonneg_left (by linarith [hx.2]) hc)
  let v : ℕ → ℝ := fun i => envelopeValue S (u, i)
  let E : ℝ := 2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ)
  have hv : ∀ i < grid.length,
      |v i - integrand S s ((a : ℝ) + i * h)| ≤ E := by
    intro i hi
    have hnode : 0 ≤ envelopeNode (u, i) := by
      change 0 ≤ a + (i : ℚ) * h
      exact add_nonneg ha.1 (mul_nonneg (Nat.cast_nonneg _) hh)
    have he := envelopeValue_error S s t d grid fuel hd hd1 hf i hnode
    simpa only [envelopeNode, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] using he
  have hr := rectangleRule_numeric_error (integrand S s) v a h (1 + 1 / (s : ℝ)) E
    grid.length hhR hint hmod hv
  rw [hend] at hr
  have hInt : (∫ x in (a : ℝ)..(s : ℝ), integrand S s x) = phis S s t - phi S t := by
    rw [hleft]
    exact (discrepancy_integral S hS hs t).symm
  rw [hInt] at hr
  have hcode : (envelopeWithFuel S u : ℝ) =
      (h : ℝ) * ∑ i ∈ Finset.range grid.length, v i := by
    simp only [envelopeWithFuel, siteNumbers, map_range_eq_ofFn, List.sum_ofFn,
      Rat.cast_mul, Rat.cast_sum]
    exact congrArg (fun z : ℝ => (h : ℝ) * z)
      (Fin.sum_univ_eq_sum_range v grid.length)
  rw [← hcode] at hr
  exact hr



end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic







theorem unitProduct_length (u : List Unit × List Unit) :
    (unitProduct u).length = u.1.length * u.2.length := by
  simp [unitProduct, List.length_flatMap]





theorem unitPower_length (n : ℕ) (xs : List Unit) : (unitPower n xs).length = xs.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [unitPower, unitProduct_length, ih, pow_succ]





theorem polynomialFuel_length (C n : ℕ) (sites : List Unit) :
    (polynomialFuel C n sites).length = C * (sites.length + 1) ^ n := by
  simp [polynomialFuel, unitProduct_length, unitPower_length]





theorem boundedPower_correct (b : ℕ) (fuel : List Unit) (n : ℕ) (hn : n ≤ fuel.length) :
    boundedPower b (fuel, n) = b ^ n := by
  have hp (xs : List Unit) : (xs.map (fun _ => b)).prod = b ^ xs.length := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih, pow_succ, mul_comm]
  simp only [boundedPower, naturalProduct_eq, hp, List.length_take, Nat.min_eq_left hn]

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section
































































end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Matrix

theorem approximatePSDTest_spec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (d e : ℚ) (fuel : List Unit) :
    approximatePSDTest
      ((((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d), fuel), e) = true ↔
        ∀ i j, |(A - (roundedMatrixSqrt A d fuel.length) ^ 2) i j| ≤ e := by
  rw [approximatePSDTest, rootCompute_correct, rootResidualTest_correct]

theorem castM_symm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (hA : A.IsSymm) :
    (castM A).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  apply Matrix.IsSymm.ext
  intro i j
  change (A j i : ℝ) = (A i j : ℝ)
  exact_mod_cast hA.apply i j

theorem approximatePSDTest_sound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : A.IsSymm) (d e : ℚ) (he : 0 ≤ e) (fuel : List Unit)
    (htest : approximatePSDTest
      ((((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d), fuel), e) = true) :
    (castM A + ((N : ℝ) ^ 2 * (e : ℝ)) •
      (1 : Matrix (Fin N) (Fin N) ℝ)).PosSemidef := by
  have hr := (approximatePSDTest_spec A d e fuel).mp htest
  let Y := roundedMatrixSqrt A d fuel.length
  have hY := castM_symm Y (roundedMatrixSqrt_symm A hA d fuel.length)
  apply approximate_square_root_psd (castM A) (castM Y) (castM_symm A hA) hY e
    (by exact_mod_cast he)
  intro i j
  have hcast : castM (A - Y ^ 2) = castM A - (castM Y) ^ 2 := by
    rw [castM_subQ, pow_two, pow_two, castM_mulQ]
  rw [← hcast]
  change |((A - Y ^ 2) i j : ℝ)| ≤ e
  exact_mod_cast hr i j

theorem tolerance_residual_budget (N T : ℕ) (e : ℝ) (he : 0 < e)
    (hT : 8 ≤ e * ((T : ℝ) + 2)) :
    4 / ((T : ℝ) + 2) + 4 * (N : ℝ) *
      ((e / (8 * ((N : ℝ) + 1) * ((T : ℝ) + 1) * (1 + 2 * (N : ℝ)) ^ T)) *
        T * (1 + 2 * (N : ℝ)) ^ T) ≤ e := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hq : 0 < (1 + 2 * (N : ℝ)) ^ T := by positivity
  have hf : 4 / ((T : ℝ) + 2) ≤ e / 2 := by
    rw [div_le_iff₀ (by positivity : 0 < (T : ℝ) + 2)]
    nlinarith
  have hfn : 0 ≤ (N : ℝ) / ((N : ℝ) + 1) ∧ (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith)
  have hft : 0 ≤ (T : ℝ) / ((T : ℝ) + 1) ∧ (T : ℝ) / ((T : ℝ) + 1) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith)
  have hsecond : 4 * (N : ℝ) *
      ((e / (8 * ((N : ℝ) + 1) * ((T : ℝ) + 1) * (1 + 2 * (N : ℝ)) ^ T)) *
        T * (1 + 2 * (N : ℝ)) ^ T) ≤ e / 2 := by
    have hid : 4 * (N : ℝ) *
      ((e / (8 * ((N : ℝ) + 1) * ((T : ℝ) + 1) * (1 + 2 * (N : ℝ)) ^ T)) *
        T * (1 + 2 * (N : ℝ)) ^ T) =
        (e / 2) * ((N : ℝ) / ((N : ℝ) + 1)) * ((T : ℝ) / ((T : ℝ) + 1)) := by
      field_simp
      <;> ring
    rw [hid]
    have hh := mul_le_mul hfn.2 hft.2 hft.1 (by norm_num : (0 : ℝ) ≤ 1)
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ e / 2)
    simpa only [one_mul, mul_one, mul_assoc] using hm
  linarith

theorem approximatePSDTest_complete {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : (castM A).PosSemidef)
    (hA1 : ((1 : Matrix (Fin N) (Fin N) ℝ) - castM A).PosSemidef)
    (e : ℚ) (he : 0 < e) (fuel : List Unit)
    (hT : 8 ≤ (e : ℝ) * ((fuel.length : ℝ) + 2)) :
    approximatePSDTest
      ((((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()),
        rootTolerance ((List.replicate N (), fuel), e)), fuel), e) = true := by
  let d := rootTolerance ((List.replicate N (), fuel), e)
  have hd : d = e / (8 * ((N : ℚ) + 1) * ((fuel.length : ℚ) + 1) *
      (1 + 2 * (N : ℚ)) ^ fuel.length) := by
    dsimp only [d]
    rw [rootTolerance_formula, List.length_replicate]
  have hd0 : 0 < d := by rw [hd]; positivity
  apply (approximatePSDTest_spec A d e fuel).mpr
  intro i j
  have hr := roundedMatrixSqrt_residual A hA hA1 d hd0 fuel.length i j
  have hb := tolerance_residual_budget N fuel.length e (by exact_mod_cast he) hT
  have hdR : (d : ℝ) = (e : ℝ) / (8 * ((N : ℝ) + 1) * ((fuel.length : ℝ) + 1) *
      (1 + 2 * (N : ℝ)) ^ fuel.length) := by exact_mod_cast hd
  rw [hdR] at hr
  have hc : castM (A - (roundedMatrixSqrt A d fuel.length) ^ 2) =
      castM A - (castM (roundedMatrixSqrt A d fuel.length)) ^ 2 := by
    rw [castM_subQ, pow_two, pow_two, castM_mulQ]
  have hh := hr.trans hb
  rw [← hc] at hh
  change |((A - (roundedMatrixSqrt A d fuel.length) ^ 2) i j : ℝ)| ≤ (e : ℝ) at hh
  exact_mod_cast hh

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessPSD
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled



def shiftMatrix {N : ℕ} (S : SpinLaw) (J : Matrix (Fin N) (Fin N) ℚ) (u : ℚ) :
    Matrix (Fin N) (Fin N) ℚ :=
  fun i j => ((if i = j then u else 0) - J i j) / fixedScale S

theorem fixedScale_cast (S : SpinLaw) : (fixedScale S : ℝ) = 2 * tau S + 1 := by
  simp [fixedScale, tau]

theorem fixedScale_pos (S : SpinLaw) : 0 < fixedScale S := by
  have hh := EnvelopeAnalysis.tau_pos S
  change (0 : ℝ) < (tauQ S : ℝ) at hh
  have ht : (0 : ℚ) < tauQ S := by exact_mod_cast hh
  unfold fixedScale
  positivity

theorem normalizedShift_encoded {N : ℕ} (S : SpinLaw)
    (J : Matrix (Fin N) (Fin N) ℚ) (u : ℚ) :
    normalizedShift S (encodedInput J, u) = List.ofFn (fun i => List.ofFn (shiftMatrix S J u i)) := by
  simp only [normalizedShift, encodedInput, siteNumbers, List.length_replicate, map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp only [matrixEntry_ofFn, shiftMatrix, Fin.val_inj]

theorem cast_shiftMatrix {N : ℕ} (S : SpinLaw) (J : Matrix (Fin N) (Fin N) ℚ) (u : ℚ) :
    castM (shiftMatrix S J u) = (1 / (fixedScale S : ℝ)) •
      ((u : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM J) := by
  ext i j
  by_cases hij : i = j <;> simp [castM, shiftMatrix, Matrix.one_apply, hij, div_eq_mul_inv, mul_comm]

theorem shiftMatrix_symm {N : ℕ} (S : SpinLaw) (J : Matrix (Fin N) (Fin N) ℚ)
    (hJ : J.IsSymm) (u : ℚ) : (shiftMatrix S J u).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [shiftMatrix, hJ.apply i j]
  by_cases hij : i = j
  · subst j; rfl
  · simp [hij, Ne.symm hij]

theorem scalar_shift_mono {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ)
    {u v : ℝ} (huv : u ≤ v) (h : (u • (1 : Matrix (Fin N) (Fin N) ℝ) - J).PosSemidef) :
    (v • (1 : Matrix (Fin N) (Fin N) ℝ) - J).PosSemidef := by
  have hh := h.add ((Matrix.PosSemidef.one (n := Fin N) (R := ℝ)).smul (sub_nonneg.mpr huv))
  have he : u • (1 : Matrix (Fin N) (Fin N) ℝ) - J + (v-u) • 1 = v • 1 - J := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rwa [he] at hh

theorem candidateLevel_cast {N : ℕ} (S : SpinLaw) (C j : ℕ) :
    (candidateLevel S C (List.replicate N (), j) : ℝ) =
      tau S * (1 + (j : ℝ) / ((C : ℝ) * ((N : ℝ) + 1))) := by
  simp only [candidateLevel, polynomialFuel_length, List.length_replicate, pow_one]
  push_cast
  rfl

theorem preTolerance_cast {N : ℕ} (C : ℕ) :
    (preTolerance C (List.replicate N ()) : ℝ) = 1 / ((C : ℝ) * ((N : ℝ) + 1) ^ 3) := by
  simp [preTolerance]



end CritWinSpin.Implementation.PreprocessPSD
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessSelection
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessPSD

theorem preBuffer_cast (N : ℕ) : (preBuffer (List.replicate N ()) : ℝ) =
    1 / (1000 * ((N : ℝ) + 1)) := by simp [preBuffer]

theorem first_true_le {p : ℕ → Bool} {M j : ℕ} (hp : p j = true) :
    (List.range (M+1)).findIdx p ≤ j := by
  by_contra hn
  have hlt : j < (List.range (M+1)).findIdx p := Nat.lt_of_not_ge hn
  have hh := List.not_of_lt_findIdx hlt
  simp only [List.getElem_range] at hh
  rw [hp] at hh
  contradiction

theorem first_true_spec {p : ℕ → Bool} {M : ℕ} (hp : p M = true) :
    (List.range (M+1)).findIdx p ≤ M ∧ p ((List.range (M+1)).findIdx p) = true := by
  have hle := first_true_le (M := M) hp
  have hidx : (List.range (M+1)).findIdx p < (List.range (M+1)).length := by
    rw [List.length_range]
    omega
  have hh := @List.findIdx_getElem ℕ p (List.range (M+1)) hidx
  simp only [List.getElem_range] at hh
  exact ⟨hle, hh⟩

theorem selectedIndex_eq (S : SpinLaw) (C : ℕ) (u : PreInput) :
    (preTests S C u).findIdx id =
      (List.range ((polynomialFuel C 1 u.2).length + 1)).findIdx (fun j => candidatePSD S C (u,j)) := by
  simp only [preTests, siteNumbers, List.length_cons, List.findIdx_map, Function.comp_def, id_eq]

theorem pre_error_budget (S : SpinLaw) (C N : ℕ)
    (hC : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ)) :
    (fixedScale S : ℝ) * (N : ℝ) ^ 2 * (preTolerance C (List.replicate N ()) : ℝ) ≤
      (preBuffer (List.replicate N ()) : ℝ) := by
  have hH : (0 : ℝ) < fixedScale S := by exact_mod_cast fixedScale_pos S
  have hCp : (0 : ℝ) < C := by nlinarith only [hC, hH]
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [preTolerance_cast, preBuffer_cast]
  have he : (fixedScale S : ℝ) * (N : ℝ) ^ 2 * (1 / ((C : ℝ) * ((N : ℝ) + 1) ^ 3)) =
      ((fixedScale S : ℝ) * (N : ℝ) ^ 2) / ((C : ℝ) * ((N : ℝ) + 1) ^ 3) := by ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < C * ((N : ℝ) + 1) ^ 3)
    (by positivity : (0 : ℝ) < 1000 * ((N : ℝ) + 1))).2
  have h₁ := mul_le_mul_of_nonneg_right hC (sq_nonneg (N : ℝ))
  have h₂ := mul_le_mul_of_nonneg_left
    (show (N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 by nlinarith only [hN]) hCp.le
  have hh := mul_le_mul_of_nonneg_right (h₁.trans h₂) hNp.le
  nlinarith only [hh]

theorem candidatePSD_sound {N : ℕ} (S : SpinLaw) (C j : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hJ : J.IsSymm)
    (hC : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ))
    (htest : candidatePSD S C (encodedInput J, j) = true) :
    (((candidateLevel S C (List.replicate N (), j) : ℝ) +
      (preBuffer (List.replicate N ()) : ℝ)) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM J).PosSemidef := by
  let u := candidateLevel S C (List.replicate N (), j)
  let A := shiftMatrix S J u
  let fuel := polynomialFuel (C*C) 3 (List.replicate N ())
  let e := preTolerance C (List.replicate N ())
  let d := rootTolerance ((List.replicate N (), fuel), e)
  let H : ℝ := fixedScale S
  have hHp : 0 < H := by
    change (0 : ℝ) < (fixedScale S : ℝ)
    exact_mod_cast fixedScale_pos S
  have hCp : (0 : ℝ) < C := by dsimp [H] at hHp; nlinarith only [hC, hHp]
  have he : 0 ≤ e := by
    dsimp [e, preTolerance]
    have hc : (0 : ℚ) < C := by exact_mod_cast hCp
    positivity
  have ht : approximatePSDTest ((((List.ofFn (fun i => List.ofFn (A i)), List.replicate N ()), d), fuel), e) = true := by
    simpa only [candidatePSD, normalizedShift_encoded] using htest
  have hPSD := approximatePSDTest_sound A (shiftMatrix_symm S J hJ u) d e he fuel ht
  have hScaled := hPSD.smul hHp.le
  have hEq : H • (castM A + ((N : ℝ) ^ 2 * (e : ℝ)) •
      (1 : Matrix (Fin N) (Fin N) ℝ)) =
        ((u : ℝ) + H * (N : ℝ) ^ 2 * (e : ℝ)) • 1 - castM J := by
    rw [show A = shiftMatrix S J u from rfl, cast_shiftMatrix]
    ext i k
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    change H * ((1/H) * ((u : ℝ) * (1 : Matrix (Fin N) (Fin N) ℝ) i k - castM J i k) +
      (N : ℝ)^2 * (e : ℝ) * (1 : Matrix (Fin N) (Fin N) ℝ) i k) =
      ((u : ℝ) + H * (N : ℝ)^2 * (e : ℝ)) * (1 : Matrix (Fin N) (Fin N) ℝ) i k - castM J i k
    field_simp [hHp.ne'] <;> ring
  rw [hEq] at hScaled
  exact scalar_shift_mono (castM J) (by have hh := pre_error_budget S C N hC; change H * (N : ℝ)^2 * (e:ℝ) ≤ _ at hh; linarith only [hh]) hScaled

end CritWinSpin.Implementation.PreprocessSelection
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessBranches
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessPSD PreprocessSelection

theorem inside_eq_candidate {N : ℕ} (S : SpinLaw) (C : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) :
    preInside S C (encodedInput J) = candidatePSD S C (encodedInput J, C * (N+1)) := by
  simp only [preInside, polynomialFuel_length, List.length_replicate, pow_one]



theorem candidate_range {N : ℕ} (S : SpinLaw) (C j : ℕ) (hC : 0 < C)
    (hj : j ≤ C * (N+1)) :
    tau S ≤ (candidateLevel S C (List.replicate N (), j) : ℝ) ∧
      (candidateLevel S C (List.replicate N (), j) : ℝ) ≤ 2 * tau S := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  have hτ := EnvelopeAnalysis.tau_pos S
  have hden : 0 < (C : ℝ) * ((N : ℝ)+1) := by positivity
  have hjR : (j : ℝ) ≤ (C : ℝ) * ((N : ℝ)+1) := by exact_mod_cast hj
  have hfrac : 0 ≤ (j : ℝ) / ((C : ℝ) * ((N : ℝ)+1)) := by positivity
  have hfrac1 : (j : ℝ) / ((C : ℝ) * ((N : ℝ)+1)) ≤ 1 := (div_le_one hden).2 hjR
  have h₀ := mul_nonneg hτ.le hfrac
  have h₁ := mul_le_mul_of_nonneg_left hfrac1 hτ.le
  rw [candidateLevel_cast]
  constructor <;> nlinarith only [h₀, h₁]



theorem selected_index_spec {N : ℕ} (S : SpinLaw) (C : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hin : preInside S C (encodedInput J) = true) :
    (preTests S C (encodedInput J)).findIdx id ≤ C * (N+1) ∧
      candidatePSD S C (encodedInput J, (preTests S C (encodedInput J)).findIdx id) = true := by
  rw [inside_eq_candidate] at hin
  have hh := first_true_spec (p := fun j => candidatePSD S C (encodedInput J, j)) (M := C * (N+1)) hin
  rw [selectedIndex_eq, polynomialFuel_length, List.length_replicate, pow_one]
  exact hh

theorem selected_level_eq {N : ℕ} (S : SpinLaw) (C : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) :
    (preSelectedLevel S C (encodedInput J) : ℝ) =
      (candidateLevel S C (List.replicate N (), (preTests S C (encodedInput J)).findIdx id) : ℝ) +
        2 * (preBuffer (List.replicate N ()) : ℝ) := by
  simp only [preSelectedLevel, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]

theorem selected_bounds {N : ℕ} (S : SpinLaw) (C : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hJ : J.IsSymm) (hC8 : 8 ≤ C)
    (hC : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ))
    (hin : preInside S C (encodedInput J) = true) :
    tau S + 2 * (preBuffer (List.replicate N ()) : ℝ) ≤ (preSelectedLevel S C (encodedInput J) : ℝ) ∧
    (preSelectedLevel S C (encodedInput J) : ℝ) ≤ 2 * tau S + 1 ∧
    (((preSelectedLevel S C (encodedInput J) : ℝ) - (preBuffer (List.replicate N ()) : ℝ)) •
      (1 : Matrix (Fin N) (Fin N) ℝ) - castM J).PosSemidef := by
  obtain ⟨hle, htest⟩ := selected_index_spec S C J hin
  have hr := candidate_range S C _ (show 0 < C by omega) hle
  have hlevel := selected_level_eq S C J
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbuf : (preBuffer (List.replicate N ()) : ℝ) ≤ 1/1000 := by
    rw [preBuffer_cast]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hN])
  refine ⟨by linarith only [hr.1, hlevel], by linarith only [hr.2, hlevel, hbuf], ?_⟩
  have hpsd := candidatePSD_sound S C _ J hJ hC htest
  have he : (preSelectedLevel S C (encodedInput J) : ℝ) - (preBuffer (List.replicate N ()) : ℝ) =
      (candidateLevel S C (List.replicate N (), (preTests S C (encodedInput J)).findIdx id) : ℝ) +
        (preBuffer (List.replicate N ()) : ℝ) := by linarith only [hlevel]
  rw [he]
  exact hpsd

end CritWinSpin.Implementation.PreprocessBranches
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessIntegral
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches





theorem spinErrorCoefficient_nonneg (S : SpinLaw) : 0 ≤ spinErrorCoefficient S := by
  have hρ : (0 : ℝ) < S.ρ 1 := by exact_mod_cast S.pos 1 S.one_mem
  unfold spinErrorCoefficient
  positivity

theorem precision_cast (C N : ℕ) : (preIntegralPrecision C (List.replicate N ()) : ℝ) =
    1 / ((C : ℝ) * ((N : ℝ)+1)) := by simp [preIntegralPrecision]

theorem integration_fuel (C N : ℕ) (hC : 8 ≤ C) :
    2 / (preIntegralPrecision C (List.replicate N ()) : ℝ) ^ 3 + 2 ≤
      ((polynomialFuel (C ^ 4) 3 (List.replicate N ())).length : ℝ) := by
  have hc : (8 : ℝ) ≤ C := by exact_mod_cast hC
  have hcp : (0 : ℝ) < C := by linarith only [hc]
  have hn : 1 ≤ (N : ℝ)+1 := by
    have hh : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith only [hh]
  have hnp : 0 < (N : ℝ)+1 := by positivity
  rw [precision_cast, polynomialFuel_length, List.length_replicate]
  push_cast
  have he : 2 / (1 / ((C : ℝ) * ((N : ℝ)+1))) ^ 3 =
      2 * (C : ℝ) ^ 3 * ((N : ℝ)+1) ^ 3 := by
    field_simp [hcp.ne', hnp.ne'] <;> ring
  rw [he]
  have hc3 : 1 ≤ (C : ℝ) ^ 3 := one_le_pow₀ (by linarith only [hc])
  have hn3 : 1 ≤ ((N : ℝ)+1) ^ 3 := one_le_pow₀ hn
  have hp : 1 ≤ (C : ℝ) ^ 3 * ((N : ℝ)+1) ^ 3 := by nlinarith [mul_le_mul hc3 hn3 (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ (C : ℝ) ^ 3)]
  have hh := mul_le_mul (show (2 : ℝ) ≤ (C : ℝ)-2 by linarith only [hc]) hp
    (by norm_num : (0:ℝ) ≤ 1) (by linarith only [hc] : (0:ℝ) ≤ (C : ℝ)-2)
  nlinarith only [hh]

theorem preIntegral_error {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hC : 8 ≤ C)
    (hPrecision : 1000 * integrationConstant S ≤ (C : ℝ))
    (hs : tau S < (preSelectedLevel S C (encodedInput J) : ℝ))
    (hu : (preSelectedLevel S C (encodedInput J) : ℝ) ≤ 2 * tau S + 1) :
    |(preIntegral S C (encodedInput J) : ℝ) -
      ds S (preSelectedLevel S C (encodedInput J)) 0| ≤ (preBuffer (List.replicate N ()) : ℝ) := by
  let s := preSelectedLevel S C (encodedInput J)
  let d := preIntegralPrecision C (List.replicate N ())
  let grid := polynomialFuel C 1 (List.replicate N ())
  let fuel := polynomialFuel (C ^ 4) 3 (List.replicate N ())
  have hcp : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hn : 0 < grid.length := by dsimp [grid]; rw [polynomialFuel_length, List.length_replicate]; positivity
  have hnr : (0 : ℝ) < grid.length := by exact_mod_cast hn
  have hGrid : (grid.length : ℝ) = (C : ℝ) * ((N : ℝ)+1) := by
    dsimp [grid]
    rw [polynomialFuel_length, List.length_replicate, pow_one]
    push_cast
    rfl
  have hdR : (d : ℝ) = 1 / (grid.length : ℝ) := by
    dsimp [d]
    rw [precision_cast, hGrid]
  have hd : 0 < d := by
    have hh : (0 : ℝ) < d := by rw [hdR]; positivity
    exact_mod_cast hh
  have hd1 : d ≤ 1 := by
    have hc1 : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
    have hlen : (1 : ℝ) ≤ grid.length := by exact_mod_cast hn
    have hh : (d : ℝ) ≤ 1 := by rw [hdR]; exact (div_le_one hnr).2 hlen
    exact_mod_cast hh
  have hspos : (0 : ℝ) < s := (EnvelopeAnalysis.tau_pos S).trans hs
  have hsQ : 0 < s := by exact_mod_cast hspos
  have hf := integration_fuel C N hC
  change 2 / (d : ℝ)^3 + 2 ≤ (fuel.length : ℝ) at hf
  have hr := envelopeWithFuel_error S hS s 0 d hs grid fuel hn hd hd1 hf
  have hcode : preIntegral S C (encodedInput J) = envelopeWithFuel S (((s,0,d),grid),fuel) := rfl
  rw [← hcode] at hr
  simp only [Rat.cast_zero] at hr
  rw [← EnvelopeIntegral.discrepancy_eq S (s : ℝ) 0] at hr
  have hMesh : (envelopeMesh (((s,0,d),grid),fuel) : ℝ) = (s : ℝ) / (grid.length : ℝ) := by
    change (((s - envelopeLeft (s,0)) / (grid.length : ℚ) : ℚ) : ℝ) = _
    rw [envelopeLeft_eq]
    simp only [abs_zero, min_eq_left hsQ.le, sub_zero, Rat.cast_div, Rat.cast_natCast]
  rw [hMesh] at hr
  have hρ : (0 : ℝ) < S.ρ 1 := by exact_mod_cast S.pos 1 S.one_mem
  have hFactor : (grid.length : ℝ) *
      ((1 + 1/(s:ℝ)) * ((s:ℝ)/(grid.length:ℝ))^2 + ((s:ℝ)/(grid.length:ℝ)) *
        (2 * (Fintype.card {x : ℚ // x ∈ S.A} : ℝ) * (d:ℝ) / (S.ρ 1 : ℝ))) =
      ((s:ℝ)^2 + (s:ℝ) + spinErrorCoefficient S * (s:ℝ)) / (grid.length:ℝ) := by
    rw [hdR]
    unfold spinErrorCoefficient
    field_simp [hspos.ne', hnr.ne', hρ.ne'] <;> ring
  rw [hFactor] at hr
  have hsH : (s : ℝ) ≤ (fixedScale S : ℝ) := by rw [fixedScale_cast]; exact hu
  have hNumer : (s:ℝ)^2 + (s:ℝ) + spinErrorCoefficient S * (s:ℝ) ≤ integrationConstant S := by
    have h₂ := pow_le_pow_left₀ hspos.le hsH 2
    have h₃ := mul_le_mul_of_nonneg_left hsH (spinErrorCoefficient_nonneg S)
    unfold integrationConstant
    nlinarith only [h₂, h₃, hsH]
  have hFinal : integrationConstant S / (grid.length : ℝ) ≤ (preBuffer (List.replicate N ()) : ℝ) := by
    rw [hGrid, preBuffer_cast]
    apply (div_le_div_iff₀ (by positivity : 0 < (C:ℝ)*((N:ℝ)+1))
      (by positivity : 0 < 1000*((N:ℝ)+1))).2
    have hh := mul_le_mul_of_nonneg_right hPrecision (show (0:ℝ) ≤ (N:ℝ)+1 by positivity)
    nlinarith only [hh]
  exact hr.trans ((div_le_div_of_nonneg_right hNumer hnr.le).trans hFinal)

end CritWinSpin.Implementation.PreprocessIntegral
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.EulerFiniteBudget
open CritWinSpin.LocalTM2.Compiled EulerAnalyticStep PreprocessIntegral

theorem stepError_budget {N : ℕ} (S : SpinLaw) (D : EulerData N) {R B : ℝ}
    (hR : 2 ≤ R) (hN : (N:ℝ)+1 ≤ R) (hB0 : 0 ≤ B) (hB : B ≤ R)
    (hK : spinErrorCoefficient S ≤ R)
    (hSigma : (D.sigma:ℝ) = 1/(2048*R^4))
    (hPhi : (D.dPhi:ℝ) = 1/R^100) (hSnap : (D.snap:ℝ) = 1/R^100)
    (hRound : (D.dRound:ℝ) = 1/R^100) (hQuality : (D.k:ℝ) = R^100) :
    stepError S D B ≤ (D.sigma:ℝ)^2/(16*R^3) := by
  have he : 2*(Fintype.card {x : ℚ // x ∈ S.A}:ℝ)*(D.dPhi:ℝ)/(S.ρ 1:ℝ) =
      spinErrorCoefficient S*(D.dPhi:ℝ) := by unfold spinErrorCoefficient; ring
  unfold stepError driftError
  rw [he,hSigma,hPhi,hSnap,hRound,hQuality]
  exact EulerPrecisionArithmetic.error_budget hR (Nat.cast_nonneg N) hN hB0 hB
    (spinErrorCoefficient_nonneg S) hK

end CritWinSpin.Implementation.EulerFiniteBudget
end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp
open scoped BigOperators NNReal
open CritWinSpin

namespace CritWinSpin.Implementation.SpinKernel

open EnvelopeAnalysis

theorem tilt_sum_one (S : SpinLaw) (t : ℝ) :
    ∑ a : {x : ℚ // x ∈ S.A}, tilt S t (a : ℚ) = 1 := by
  unfold tilt
  have heq : (∑ a : {x : ℚ // x ∈ S.A}, (S.ρ (a : ℚ) : ℝ) * Real.exp (t * ((a : ℚ) : ℝ) - phi S t)) =
      ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ) - phi S t) :=
    Finset.sum_coe_sort S.A (fun x => (S.ρ x : ℝ) * Real.exp (t * (x : ℝ) - phi S t))
  rw [heq]
  have hfac : ∀ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ) - phi S t) =
      Real.exp (-phi S t) * ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) := by
    intro x _
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  change Real.exp (-phi S t) * mgf S t = 1
  unfold phi
  change Real.exp (-Real.log (mgf S t)) * mgf S t = 1
  rw [Real.exp_neg, Real.exp_log (mgf_pos S t), inv_mul_cancel₀ (mgf_pos S t).ne']

theorem tilt_nonneg (S : SpinLaw) (t : ℝ) (a : {x : ℚ // x ∈ S.A}) :
    0 ≤ tilt S t (a : ℚ) := by
  unfold tilt
  have hρ : 0 ≤ (S.ρ (a : ℚ) : ℝ) := by exact_mod_cast (S.pos _ a.2).le
  positivity

theorem condP_distribution {N : ℕ} (S : SpinLaw) (L : Matrix (Fin N) (Fin N) ℝ)
    (h z : Fin N → ℝ) : IsDistribution (condP S L h z) := by
  constructor
  · intro x
    exact Finset.prod_nonneg fun i _ => tilt_nonneg S _ (x i)
  · unfold condP
    rw [← Fintype.prod_sum (fun i : Fin N => fun a : {x : ℚ // x ∈ S.A} =>
      tilt S (L.mulVec z i + h i) (a : ℚ))]
    simp only [tilt_sum_one, Finset.prod_const_one]

theorem potential_gap {N : ℕ} (S : SpinLaw) (s : ℝ) (L : Matrix (Fin N) (Fin N) ℝ)
    (h z : Fin N → ℝ) :
    hsV S L h z - Wpot S s L h z = ∑ i, ds S s (L.mulVec z i + h i) := by
  unfold hsV Wpot ds fs phis
  simp only [Finset.sum_sub_distrib]
  ring

theorem kernel_distribution {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (L : Matrix (Fin N) (Fin N) ℝ) (h z : Fin N → ℝ) :
    IsDistribution (kernelK S s L h z) := by
  have hgap : 0 ≤ hsV S L h z - Wpot S s L h z := by
    rw [potential_gap]
    exact Finset.sum_nonneg fun i _ => ds_nonneg S hS hs _
  have he : Real.exp (-(hsV S L h z - Wpot S s L h z)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hgap)
  have hcond := condP_distribution S L h z
  constructor
  · intro x
    cases x with
    | none => exact sub_nonneg.mpr he
    | some x => exact mul_nonneg (Real.exp_pos _).le (hcond.1 x)
  · simp only [Fintype.sum_option, kernelK, ← Finset.mul_sum, hcond.2]
    ring



theorem pointKernel_tv_lipschitz {N : ℕ} (S : SpinLaw) (s : ℝ)
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) (C : ℝ)
    (hLip : ∀ z w : Fin N → ℝ, tvDist (kernelK S s L h z) (kernelK S s L h w) ≤
      C * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w)))
    (z w : EnvelopeGeometry.Point N) :
    tvDist (pointKernel S s L h z) (pointKernel S s L h w) ≤ (C * Real.sqrt (N : ℝ)) * dist z w := by
  have hh := hLip (fun i => z i) (fun i => w i)
  have hn : normSq ((fun i => z i) - fun i => w i) = ‖z - w‖ ^ 2 := by
    change normSq (fun i => z i - w i) = ‖z - w‖ ^ 2
    simpa only [PiLp.sub_apply] using EnvelopeGeometry.normSq_coe (z - w)
  rw [hn, Real.sqrt_sq (norm_nonneg _)] at hh
  simpa only [pointKernel, dist_eq_norm, mul_assoc] using hh

theorem coordinate_tv_bound {A : Type*} [Fintype A] (P Q : A → ℝ) (a : A) :
    |P a - Q a| ≤ 2 * tvDist P Q := by
  have hh := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset A)) => abs_nonneg (P b - Q b))
    (Finset.mem_univ a)
  unfold tvDist
  linarith

theorem pointKernel_coordinate_measurable {N : ℕ} (S : SpinLaw) (s : ℝ)
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ z w : Fin N → ℝ, tvDist (kernelK S s L h z) (kernelK S s L h w) ≤
      C * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w)))
    (a : Option (Config S (Fin N))) : Measurable (fun z : EnvelopeGeometry.Point N => pointKernel S s L h z a) := by
  have hl : LipschitzWith ⟨2 * (C * Real.sqrt (N : ℝ)), by positivity⟩
      (fun z : EnvelopeGeometry.Point N => pointKernel S s L h z a) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Real.dist_eq]
    have hc := coordinate_tv_bound (pointKernel S s L h z) (pointKernel S s L h w) a
    have hk := pointKernel_tv_lipschitz S s L h C hLip z w
    change |pointKernel S s L h z a - pointKernel S s L h w a| ≤
      2 * (C * Real.sqrt (N : ℝ)) * dist z w
    linarith
  exact hl.continuous.measurable



end CritWinSpin.Implementation.SpinKernel

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp

namespace CritWinSpin.Implementation.DensityKernelTV

variable {X A : Type*} [MeasurableSpace X] [Fintype A]

theorem contraction (μ : Measure X) (f g : X → ℝ) (hif : Integrable f μ) (hig : Integrable g μ)
    (K : X → A → ℝ) (hK : ∀ x, IsDistribution (K x))
    (hmK : ∀ a, Measurable (fun x => K x a)) :
    tvDist (fun a => ∫ x, f x * K x a ∂μ) (fun a => ∫ x, g x * K x a ∂μ) ≤
      (∫ x, |f x - g x| ∂μ) / 2 := by
  classical
  have hKb (a : A) : ∀ x, ‖K x a‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg ((hK x).1 a)]
    exact (Finset.single_le_sum (fun b _ => (hK x).1 b) (Finset.mem_univ a)).trans_eq (hK x).2
  have hiF (a : A) : Integrable (fun x => f x * K x a) μ :=
    hif.mul_bdd (hmK a).aestronglyMeasurable (Filter.Eventually.of_forall (hKb a))
  have hiG (a : A) : Integrable (fun x => g x * K x a) μ :=
    hig.mul_bdd (hmK a).aestronglyMeasurable (Filter.Eventually.of_forall (hKb a))
  have hiAbs (a : A) : Integrable (fun x => |f x - g x| * K x a) μ :=
    (hif.sub hig).abs.mul_bdd (hmK a).aestronglyMeasurable (Filter.Eventually.of_forall (hKb a))
  have hp (a : A) : |(∫ x, f x * K x a ∂μ) - ∫ x, g x * K x a ∂μ| ≤
      ∫ x, |f x - g x| * K x a ∂μ := by
    rw [← integral_sub (hiF a) (hiG a)]
    have he : (fun x => f x * K x a - g x * K x a) = fun x => (f x - g x) * K x a := by
      funext x; ring
    rw [he]
    have hh := norm_integral_le_integral_norm (μ := μ) (f := fun x => (f x - g x) * K x a)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((hK _).1 a)] at hh
    exact hh
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hp a)
  rw [← integral_finsetSum _ (fun a _ => hiAbs a)] at hs
  have he : (fun x => ∑ a, |f x - g x| * K x a) = fun x => |f x - g x| := by
    funext x
    rw [← Finset.mul_sum, (hK x).2, mul_one]
  rw [he] at hs
  unfold tvDist
  linarith only [hs]

end CritWinSpin.Implementation.DensityKernelTV
end

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CritWinSpin.Implementation.FiniteRetry
open IsingLTL.BeliefProp

variable {A : Type} [Fintype A]









theorem distribution_atom_le_one {r : Option A → ℝ} (hr : IsDistribution r) (x : Option A) :
    r x ≤ 1 := by
  rw [← hr.2]
  exact Finset.single_le_sum (fun y _ => hr.1 y) (Finset.mem_univ x)

theorem next_distribution {r p : Option A → ℝ} (hr : IsDistribution r) (hp : IsDistribution p) :
    IsDistribution (next r p) := by
  constructor
  · intro x
    cases x with
    | none => exact mul_nonneg (hr.1 none) (hp.1 none)
    | some x => exact add_nonneg (hr.1 _) (mul_nonneg (hr.1 none) (hp.1 _))
  · have hr' := hr.2
    have hp' := hp.2
    rw [Fintype.sum_option] at hr' hp' ⊢
    simp only [next, Finset.sum_add_distrib, ← Finset.mul_sum]
    calc
      r none * p none + ((∑ x, r (some x)) + r none * ∑ i, p (some i)) =
          r none * (p none + ∑ i, p (some i)) + ∑ x, r (some x) := by ring
      _ = 1 := by rw [hp', mul_one]; exact hr' 

theorem retry_distribution {r : Option A → ℝ} (hr : IsDistribution r) (q : ℕ) :
    IsDistribution (retry r q) := by
  induction q with
  | zero =>
    constructor
    · intro z; cases z <;> norm_num [retry]
    · simp [Fintype.sum_option, retry]
  | succ q ih => exact next_distribution hr ih

theorem tv_nonneg (p q : Option A → ℝ) : 0 ≤ tvDist p q := by
  unfold tvDist
  positivity

theorem tv_triangle (p q r : Option A → ℝ) : tvDist p r ≤ tvDist p q + tvDist q r := by
  have hs := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => abs_sub_le (p z) (q z) (r z))
  rw [Finset.sum_add_distrib] at hs
  unfold tvDist
  linarith

theorem next_tv_tail {r : Option A → ℝ} (hr : IsDistribution r) (p p' : Option A → ℝ) :
    tvDist (next r p') (next r p) ≤ tvDist p' p := by
  have he (z : Option A) : |next r p' z - next r p z| = r none * |p' z - p z| := by
    have hid : next r p' z - next r p z = r none * (p' z - p z) := by
      cases z <;> simp only [next] <;> ring
    rw [hid, abs_mul, abs_of_nonneg (hr.1 none)]
  have heq : tvDist (next r p') (next r p) = r none * tvDist p' p := by
    unfold tvDist
    simp_rw [he]
    rw [← Finset.mul_sum]
    ring
  rw [heq]
  exact mul_le_of_le_one_left (tv_nonneg _ _) (distribution_atom_le_one hr none)

theorem next_tv_head (r r' : Option A → ℝ) {p : Option A → ℝ} (hp : IsDistribution p) :
    tvDist (next r' p) (next r p) ≤ tvDist r' r := by
  have hpnt (z : Option A) : |next r' p z - next r p z| ≤
      (match z with | none => 0 | some x => |r' (some x) - r (some x)|) +
        |r' none - r none| * p z := by
    cases z with
    | none =>
      simp only [next, zero_add, ← sub_mul, abs_mul, abs_of_nonneg (hp.1 none), le_refl]
    | some x =>
      have he : next r' p (some x) - next r p (some x) =
          (r' (some x) - r (some x)) + (r' none - r none) * p (some x) := by
        simp only [next]; ring
      rw [he]
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_of_nonneg (hp.1 _)])
  have hs := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hpnt z)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, mul_one] at hs
  simp only [Fintype.sum_option] at hs
  simp only [zero_add] at hs
  unfold tvDist
  simp only [Fintype.sum_option]
  linarith only [hs]

theorem retry_stability {r r' : Option A → ℝ} (hr : IsDistribution r) (hr' : IsDistribution r')
    {ε : ℝ} (he : tvDist r' r ≤ ε) (q : ℕ) :
    tvDist (retry r' q) (retry r q) ≤ (q : ℝ) * ε := by
  induction q with
  | zero => simp [tvDist, retry]
  | succ q ih =>
    have ht := tv_triangle (next r' (retry r' q)) (next r (retry r' q)) (next r (retry r q))
    have h₁ := next_tv_head r r' (retry_distribution hr' q)
    have h₂ := next_tv_tail hr (retry r q) (retry r' q)
    change tvDist (next r' (retry r' q)) (next r (retry r q)) ≤ _
    rw [Nat.cast_succ]
    nlinarith only [ht, h₁, h₂, he, ih]

theorem trial_distribution {p : A → ℝ} (hp : IsDistribution p) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : IsDistribution (trial p a) := by
  constructor
  · intro z; cases z with
    | none => exact sub_nonneg.mpr ha1
    | some x => exact mul_nonneg ha (hp.1 x)
  · simp only [Fintype.sum_option, trial, ← Finset.mul_sum, hp.2, mul_one]
    ring

theorem retry_trial_none (p : A → ℝ) (a : ℝ) (q : ℕ) :
    retry (trial p a) q none = (1 - a) ^ q := by
  induction q with
  | zero => simp [retry]
  | succ q ih => simp only [retry, next, trial, ih, pow_succ]; ring

theorem retry_trial_some (p : A → ℝ) (a : ℝ) (q : ℕ) (x : A) :
    retry (trial p a) q (some x) = (1 - (1 - a) ^ q) * p x := by
  induction q with
  | zero => simp [retry]
  | succ q ih => simp only [retry, next, trial, ih, pow_succ]; ring

theorem retry_trial_tv {p : A → ℝ} (hp : IsDistribution p) {a : ℝ} (ha1 : a ≤ 1) (q : ℕ) :
    tvDist (retry (trial p a) q) (lift p) = (1 - a) ^ q := by
  have hpow : 0 ≤ (1 - a) ^ q := pow_nonneg (sub_nonneg.mpr ha1) q
  have hs (x : A) : |retry (trial p a) q (some x) - p x| = (1 - a) ^ q * p x := by
    rw [retry_trial_some]
    have he : (1 - (1 - a) ^ q) * p x - p x = -((1 - a) ^ q * p x) := by ring
    rw [he, abs_neg, abs_of_nonneg (mul_nonneg hpow (hp.1 x))]
  unfold tvDist
  rw [Fintype.sum_option]
  simp only [lift, retry_trial_none, sub_zero, abs_of_nonneg hpow]
  simp_rw [hs]
  rw [← Finset.mul_sum, hp.2]
  ring

theorem retry_error {p : A → ℝ} (hp : IsDistribution p) {a ε : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) {r : Option A → ℝ} (hr : IsDistribution r)
    (he : tvDist r (trial p a) ≤ ε) (q : ℕ) :
    tvDist (retry r q) (lift p) ≤ (1 - a) ^ q + (q : ℝ) * ε := by
  have ht := tv_triangle (retry r q) (retry (trial p a) q) (lift p)
  have hstab := retry_stability (trial_distribution hp ha ha1) hr he q
  rw [retry_trial_tv hp ha1 q] at ht
  linarith

theorem failure_bernoulli {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (q : ℕ) :
    (1 - a) ^ q ≤ 1 / (1 + a * (q : ℝ)) := by
  have hd : 0 < 1 + a * (q : ℝ) := by positivity
  apply (le_div_iff₀ hd).2
  induction q with
  | zero => simp
  | succ q ih =>
    have hn : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
    have hs : (1 - a) * (1 + a * ((q : ℝ) + 1)) ≤ 1 + a * (q : ℝ) := by
      nlinarith [mul_nonneg (sq_nonneg a) hn]
    have hp := mul_le_mul_of_nonneg_left hs (pow_nonneg (sub_nonneg.mpr ha1) q)
    rw [pow_succ, Nat.cast_succ]
    have ih' := ih (by positivity)
    nlinarith only [hp, ih']

theorem retry_error_budget {p : A → ℝ} (hp : IsDistribution p) {a ε m : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) {r : Option A → ℝ} (hr : IsDistribution r)
    (he : tvDist r (trial p a) ≤ ε) (q : ℕ) (hm : 0 < m)
    (hq : 16 * m ≤ a * (q : ℝ)) (hε : ε ≤ 1 / (64 * m * (q : ℝ))) :
    tvDist (retry r q) (lift p) ≤ 1 / (8 * m) := by
  have hqr : 0 < (q : ℝ) := by
    by_contra hn
    have hz : (q : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg q)
    rw [hz, mul_zero] at hq
    linarith
  have hf : (1 - a) ^ q ≤ 1 / (16 * m) :=
    (failure_bernoulli ha ha1 q).trans
      (one_div_le_one_div_of_le (by positivity) (by linarith only [hq]))
  have heq : (q : ℝ) * (1 / (64 * m * (q : ℝ))) = 1 / (64 * m) := by
    field_simp [hm.ne', hqr.ne']
  have hεq := mul_le_mul_of_nonneg_left hε hqr.le
  rw [heq] at hεq
  have ht := retry_error hp ha ha1 hr he q
  have hsum : 1 / (16 * m) + 1 / (64 * m) ≤ 1 / (8 * m) := by
    have hid : 1 / (16 * m) + 1 / (64 * m) = 5 / (64 * m) := by
      field_simp [hm.ne']; ring
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0 < 64 * m) (by positivity : 0 < 8 * m)).2
    nlinarith only [hm]
  exact ht.trans ((add_le_add hf hεq).trans hsum)

end CritWinSpin.Implementation.FiniteRetry
end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp
open CritWinSpin

namespace CritWinSpin.Implementation.EnvelopeKernelTransfer
open DensityAnalysis EnvelopeGeometry ContractiveOperator

theorem trial_tv {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s a C E ε : ℝ}
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hs : tau S < s) (hC : 0 ≤ C)
    (hiW : Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z)))
    (hiU : Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S s a L h z)))
    (hreg : (1 / 2) * (∫ z : Fin N → ℝ,
      |normDens (Ualpha S s a L h) z - normDens (Wpot S s L h) z|) ≤ ε)
    (hLip : ∀ z w : Fin N → ℝ, tvDist (kernelK S s L h z) (kernelK S s L h w) ≤
      C * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w)))
    (μ : Measure (DensityAnalysis.Point N)) [IsProbabilityMeasure μ]
    (hweak : ∀ f : DensityAnalysis.Point N → ℝ,
      BoundedLip f 1 (2 * (C * Real.sqrt (N : ℝ))) →
      |(∫ z, f z ∂μ) - ∫ z, f z ∂DensityAnalysis.gibbs (potential S s a L h)| ≤ E) :
    tvDist (fun v => ∫ z, SpinKernel.pointKernel S s L h z v ∂μ)
      (fun v => ∫ z : Fin N → ℝ, normDens (Wpot S s L h) z * kernelK S s L h z v) ≤ E / 2 + ε := by
  let U := potential S s a L h
  have hiU' : Integrable (fun z : DensityAnalysis.Point N => Real.exp (-U z)) :=
    (PiVolumeTransfer.integrable_iff _).2 hiU
  letI : IsProbabilityMeasure (DensityAnalysis.gibbs U) := gibbs_probability hiU'
  have hmK := SpinKernel.pointKernel_coordinate_measurable S s L h hC hLip
  have hK := fun z : DensityAnalysis.Point N => SpinKernel.kernel_distribution S hS hs L h (fun i => z i)
  have hSample := KernelTests.mixture_tv μ (DensityAnalysis.gibbs U) hK hmK
    (SpinKernel.pointKernel_tv_lipschitz S s L h C hLip) hweak
  change tvDist (fun v => ∫ z : DensityAnalysis.Point N, SpinKernel.pointKernel S s L h z v ∂μ)
    (fun v => ∫ z : DensityAnalysis.Point N, SpinKernel.pointKernel S s L h z v ∂DensityAnalysis.gibbs U) ≤ E / 2 at hSample
  have hmRaw (v : Option (Config S (Fin N))) :
      Measurable (fun z : Fin N → ℝ => kernelK S s L h z v) := by
    have hh := (hmK v).comp (WithLp.measurable_toLp 2 (Fin N → ℝ))
    change Measurable (fun z : Fin N → ℝ => kernelK S s L h z v) at hh
    exact hh
  have hif : Integrable (normDens (Ualpha S s a L h)) := by
    change Integrable (fun z => Real.exp (-Ualpha S s a L h z) / ∫ y, Real.exp (-Ualpha S s a L h y))
    exact hiU.div_const _
  have hig : Integrable (normDens (Wpot S s L h)) := by
    change Integrable (fun z => Real.exp (-Wpot S s L h z) / ∫ y, Real.exp (-Wpot S s L h y))
    exact hiW.div_const _
  have hReg := DensityKernelTV.contraction volume (normDens (Ualpha S s a L h))
    (normDens (Wpot S s L h)) hif hig (kernelK S s L h)
    (fun z => SpinKernel.kernel_distribution S hS hs L h z) hmRaw
  have hEq (v : Option (Config S (Fin N))) :
      (∫ z : DensityAnalysis.Point N, SpinKernel.pointKernel S s L h z v ∂DensityAnalysis.gibbs U) =
        ∫ z : Fin N → ℝ, normDens (Ualpha S s a L h) z * kernelK S s L h z v := by
    have hh := PiVolumeTransfer.gibbs_integral_eq (Ualpha S s a L h)
      (fun z => kernelK S s L h z v) (continuous_potential S s a L h) hiU
    change (∫ z : DensityAnalysis.Point N, SpinKernel.pointKernel S s L h z v ∂DensityAnalysis.gibbs U) = _ at hh
    rw [hh]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => mul_comm _ _)
  have hfun : (fun v => ∫ z : DensityAnalysis.Point N,
      SpinKernel.pointKernel S s L h z v ∂DensityAnalysis.gibbs U) =
        fun v => ∫ z : Fin N → ℝ, normDens (Ualpha S s a L h) z * kernelK S s L h z v := funext hEq
  have hR : tvDist (fun v => ∫ z : DensityAnalysis.Point N,
      SpinKernel.pointKernel S s L h z v ∂DensityAnalysis.gibbs U)
      (fun v => ∫ z : Fin N → ℝ, normDens (Wpot S s L h) z * kernelK S s L h z v) ≤ ε := by
    rw [hfun]
    apply hReg.trans
    nlinarith only [hreg]
  have ht := FiniteRetry.tv_triangle
    (fun v => ∫ z, SpinKernel.pointKernel S s L h z v ∂μ)
    (fun v => ∫ z, SpinKernel.pointKernel S s L h z v ∂DensityAnalysis.gibbs U)
    (fun v => ∫ z : Fin N → ℝ, normDens (Wpot S s L h) z * kernelK S s L h z v)
  linarith only [ht, hSample, hR]

end CritWinSpin.Implementation.EnvelopeKernelTransfer
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.HubbardTrialLaw
open Matrix IsingLTL.BeliefProp



theorem gap_bounds {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (L : Matrix (Fin N) (Fin N) ℝ) (h z : Fin N → ℝ) :
    0 ≤ hsV S L h z-Wpot S s L h z ∧
      hsV S L h z-Wpot S s L h z ≤ (N:ℝ)*ds S s 0 := by
  rw [SpinKernel.potential_gap]
  constructor
  · exact Finset.sum_nonneg (fun i _ => EnvelopeAnalysis.ds_nonneg S hS hs _)
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      EnvelopeIntegral.discrepancy_le_at_zero S hS hs (L.mulVec z i+h i))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh

theorem ideal_trial {N : ℕ} (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
    (J L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) {s : ℝ}
    (hs : tau S < s) (hJ : J.PosSemidef) (hJL : J = L*L.transpose)
    (hiW : Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z))) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ Real.exp (-((N:ℝ)*ds S s 0)) ≤ α ∧
      law S s L h = FiniteRetry.trial (CritWinSpin.gibbs S J h) α := by
  obtain ⟨_,_,_,_,hHS,_,_,_⟩ := p4c_4_4_math.{0}
  obtain ⟨_,_,hData⟩ := hHS S p hS hp
  obtain ⟨_,hZ,_,hCond⟩ := hData J L h s hs hJ hJL hiW
  let Z : ℝ := ∫ z : Fin N → ℝ, Real.exp (-Wpot S s L h z)
  let f : (Fin N → ℝ) → ℝ := normDens (Wpot S s L h)
  let acc : (Fin N → ℝ) → ℝ := fun z => Real.exp (-(hsV S L h z-Wpot S s L h z))
  let α : ℝ := 1-law S s L h none
  have hf : Integrable f := by
    change Integrable (fun z => Real.exp (-Wpot S s L h z)/Z)
    exact hiW.div_const Z
  have hf0 (z : Fin N → ℝ) : 0 ≤ f z := by
    change 0 ≤ Real.exp (-Wpot S s L h z)/Z
    exact div_nonneg (Real.exp_pos _).le hZ.le
  have hf1 : (∫ z, f z) = 1 := by
    change (∫ z : Fin N → ℝ, Real.exp (-Wpot S s L h z)/Z) = 1
    rw [integral_div]
    exact div_self hZ.ne'
  have hgapCont : Continuous (fun z : Fin N → ℝ => hsV S L h z-Wpot S s L h z) := by
    simp_rw [SpinKernel.potential_gap]
    apply continuous_finset_sum
    intro i _
    apply (EnvelopeAnalysis.ds_continuous S s).comp
    unfold Matrix.mulVec dotProduct
    fun_prop
  have haccM : Measurable acc := (Real.continuous_exp.comp hgapCont.neg).measurable
  have hacc1 (z : Fin N → ℝ) : acc z ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (gap_bounds S hS hs L h z).1)
  have haccLow (z : Fin N → ℝ) : Real.exp (-((N:ℝ)*ds S s 0)) ≤ acc z :=
    Real.exp_le_exp.mpr (neg_le_neg (gap_bounds S hS hs L h z).2)
  have hfa : Integrable (fun z => f z*acc z) := by
    apply hf.mul_bdd haccM.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hacc1 z)
  have hfun : (fun z : Fin N → ℝ => normDens (Wpot S s L h) z * kernelK S s L h z none) =
      fun z => f z-f z*acc z := by
    funext z
    change f z*(1-acc z) = f z-f z*acc z
    ring
  have hαeq : α = ∫ z, f z*acc z := by
    dsimp only [α,law]
    rw [hfun,integral_sub hf hfa,hf1]
    ring
  have hLower : Real.exp (-((N:ℝ)*ds S s 0)) ≤ α := by
    have hh := integral_mono (hf.mul_const (Real.exp (-((N:ℝ)*ds S s 0)))) hfa
      (fun z => mul_le_mul_of_nonneg_left (haccLow z) (hf0 z))
    rw [integral_mul_const,hf1,one_mul,← hαeq] at hh
    exact hh
  have hα : 0 < α := (Real.exp_pos _).trans_le hLower
  have hα1 : α ≤ 1 := by
    have hn : 0 ≤ law S s L h none := integral_nonneg (fun z =>
      mul_nonneg (hf0 z) ((SpinKernel.kernel_distribution S hS hs L h z).1 none))
    dsimp only [α]
    linarith only [hn]
  refine ⟨α,hα,hα1,hLower,?_⟩
  funext v
  cases v with
  | none => change law S s L h none = 1-α; dsimp only [α]; ring
  | some x =>
    have hh := hCond x
    change law S s L h (some x)/α = CritWinSpin.gibbs S J h x at hh
    change law S s L h (some x) = α*CritWinSpin.gibbs S J h x
    have he := (div_eq_iff hα.ne').1 hh
    simpa only [mul_comm] using he

theorem retry_budget (m cap : ℕ) {α : ℝ} (hα : Real.exp (-(cap:ℝ)) ≤ α) :
    16*(m:ℝ) ≤ α*(16*(m:ℝ)*(4:ℝ)^cap) := by
  have he4 : Real.exp (1:ℝ) ≤ 4 := (Real.exp_one_lt_three).le.trans (by norm_num)
  have hp := pow_le_pow_left₀ (Real.exp_pos (1:ℝ)).le he4 cap
  rw [← Real.exp_nat_mul 1 cap] at hp
  simp only [mul_one] at hp
  have hh := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-(cap:ℝ))).le
  have hid : Real.exp (-(cap:ℝ))*Real.exp (cap:ℝ) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  rw [hid] at hh
  have hs := mul_le_mul_of_nonneg_right hα (show 0 ≤ (4:ℝ)^cap by positivity)
  have hb : 1 ≤ α*(4:ℝ)^cap := hh.trans hs
  have hm := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ 16*(m:ℝ) by positivity)
  nlinarith only [hm]

end CritWinSpin.Implementation.HubbardTrialLaw
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

















































end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section


































end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

































theorem rationalReadFold_encoded (qs : List ℚ) (us : List Unit) (hu : us.length = qs.length)
    (tail : List Bool) (acc : List ℚ) :
    us.foldl (fun s u => rationalReadStep (s, u)) (qs.flatMap encRat ++ tail, acc) =
      (tail, qs.reverse ++ acc) := by
  induction qs generalizing us acc with
  | nil => have he : us = [] := List.length_eq_zero_iff.mp hu; subst us; rfl
  | cons q qs ih =>
      cases us with
      | nil => simp at hu
      | cons u us =>
          have hul : us.length = qs.length := by simpa using hu
          rw [List.foldl_cons]
          have hp : (q :: qs).flatMap encRat ++ tail = encRat q ++ (qs.flatMap encRat ++ tail) := by
            simp only [List.flatMap_cons, List.append_assoc]
          rw [hp]
          simp only [rationalReadStep, rationalTotal_encRat]
          change us.foldl (fun s u => rationalReadStep (s, u))
            (qs.flatMap encRat ++ tail, q :: acc) = _
          rw [ih us hul (q :: acc)]
          simp [List.reverse_cons, List.append_assoc]

theorem readRationals_encoded (qs : List ℚ) (us : List Unit) (hu : us.length = qs.length)
    (tail : List Bool) : readRationals (us, qs.flatMap encRat ++ tail) = qs := by
  rw [readRationals, rationalReadFold_encoded qs us hu tail []]
  simp













def instRationals {N : ℕ} (I : Inst N) : List ℚ :=
  (List.ofFn (fun i => List.ofFn (I.1 i))).flatten ++ List.ofFn I.2

theorem instRationals_length {N : ℕ} (I : Inst N) : (instRationals I).length = N * N + N := by
  simp [instRationals, List.length_flatten, List.map_ofFn, List.sum_ofFn]

theorem flatMap_flatten {α β : Type} (xss : List (List α)) (f : α → List β) :
    xss.flatten.flatMap f = xss.flatMap (fun xs => xs.flatMap f) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => simp [List.flatMap_append, ih]

theorem encInst_flatRationals {N : ℕ} (I : Inst N) :
    encInst I = encNat N ++ (instRationals I).flatMap encRat := by
  simp only [encInst, instRationals, List.flatMap_append, flatMap_flatten,
    List.map_ofFn, ofFn_flatMap, List.append_assoc]

theorem parseInstTotal_encoded (N : ℕ) (qs : List ℚ) (hlen : qs.length = N * N + N) :
    parseInstTotal (encNat N ++ qs.flatMap encRat) = (N, qs) := by
  let xs := encNat N ++ qs.flatMap encRat
  have hw : QMCNumericRuntime.inputWidth xs = N := by
    simp [xs, encNat, List.append_assoc, QMCNumericRuntime.inputWidth_prefix]
  have ht : siteTokens xs = List.replicate N () := by
    rw [siteTokens, hw]
    simp [xs, encNat, List.append_assoc]
  have hs : (rationalSlots xs).length = qs.length := by
    rw [hlen]
    simp [rationalSlots, ht, List.length_flatMap]
  have hd : xs.drop (QMCNumericRuntime.inputWidth xs + 1) = qs.flatMap encRat := by
    rw [hw]
    simp [xs, encNat, List.drop_append, List.append_assoc]
  have hd' : xs.drop (N + 1) = qs.flatMap encRat := by simpa only [hw] using hd
  change parseInstTotal xs = _
  rw [parseInstTotal, hw, hd']
  have he := readRationals_encoded qs (rationalSlots xs) hs []
  simpa only [List.append_nil] using congrArg (fun qs => (N, qs)) he

theorem parseInstTotal_encInst {N : ℕ} (I : Inst N) :
    parseInstTotal (encInst I) = (N, instRationals I) := by
  rw [encInst_flatRationals]
  exact parseInstTotal_encoded N (instRationals I) (instRationals_length I)



end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic







theorem flatten_uniform_length {α : Type} (rows : List (List α)) (n : ℕ)
    (hrows : ∀ row ∈ rows, row.length = n) : rows.flatten.length = rows.length * n := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hr := hrows row (by simp)
      have ht : ∀ r ∈ rows, r.length = n := by intro r h; exact hrows r (by simp [h])
      simp only [List.flatten_cons, List.length_append, hr, ih ht, List.length_cons]
      ring

theorem flattened_block {α : Type} (rows : List (List α)) (n : ℕ)
    (hrows : ∀ row ∈ rows, row.length = n) (tail : List α) (i : ℕ) (hi : i < rows.length) :
    ((rows.flatten ++ tail).drop (i * n)).take n = rows[i] := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
      have hr := hrows row (by simp)
      have ht : ∀ r ∈ rows, r.length = n := by intro r h; exact hrows r (by simp [h])
      have hd : ((row :: rows).flatten ++ tail).drop n = rows.flatten ++ tail := by
        simp only [List.flatten_cons, List.append_assoc]
        rw [← hr, List.drop_left]
      cases i with
      | zero =>
          simp only [zero_mul, List.drop_zero, List.getElem_cons_zero, List.flatten_cons,
            List.append_assoc]
          rw [← hr, List.take_left]
      | succ i =>
          have hit : i < rows.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
          rw [show (i + 1) * n = n + i * n by ring, ← List.drop_drop, hd]
          exact ih ht i hit

theorem modelFromFlat_instRationals {N : ℕ} (I : Inst N) (sites : List Unit)
    (hsites : sites.length = N) :
    modelFromFlat (sites, instRationals I) = instanceListModel I := by
  let rows := List.ofFn (fun i => List.ofFn (I.1 i))
  have hrows : ∀ row ∈ rows, row.length = N := by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    exact List.length_ofFn
  have hlen : rows.flatten.length = N * N := by
    simpa only [rows, List.length_ofFn] using flatten_uniform_length rows N hrows
  apply Prod.ext
  · change (List.range sites.length).map (fun i => ((instRationals I).drop (i * sites.length)).take sites.length) = rows
    rw [hsites]
    apply List.ext_getElem
    · simp [rows]
    · intro i hi hj
      have hir : i < rows.length := by simpa [rows] using hj
      simpa only [List.getElem_map, List.getElem_range, instRationals] using
        flattened_block rows N hrows (List.ofFn I.2) i hir
  · change (instRationals I).drop (sites.length * sites.length) = List.ofFn I.2
    rw [hsites]
    change (rows.flatten ++ List.ofFn I.2).drop (N * N) = _
    rw [← hlen, List.drop_left]





theorem parseModel_encInst {N : ℕ} (I : Inst N) :
    parseModel (encInst I) = (instanceListModel I, List.replicate N ()) := by
  have hw : QMCNumericRuntime.inputWidth (encInst I) = N := by
    rw [encInst_flatRationals]
    simp [QMCNumericRuntime.inputWidth_prefix, QAlgorithms.Complexity.encNat, List.append_assoc]
  have ht : siteTokens (encInst I) = List.replicate N () := by
    rw [siteTokens, hw, encInst_flatRationals]
    simp [QAlgorithms.Complexity.encNat, List.append_assoc]
  rw [parseModel, ht, parseInstTotal_encInst]
  rw [modelFromFlat_instRationals I _ (by simp)]

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section









theorem requestParams_encoded {N : ℕ} (I : Inst N) (m : ℕ) :
    requestParams (tupleCode [encInst I, encBin m]) =
      ((instanceListModel I, List.replicate N ()), m) := by
  rw [requestParams, requestPair_tupleCode, parseModel_encInst]
  have hb := binaryTotal_encBin m []
  simpa only [List.append_nil] using congrArg
    (fun p : ℕ × List Bool => ((instanceListModel I, List.replicate N ()), p.1)) hb









def enumerationCoins (S : SpinLaw) (xs : List Bool) : ℕ := enumerationBudget S (requestParams xs)

@[fun_prop] theorem enumerationCoins_poly (S : SpinLaw) : Poly (enumerationCoins S) := by
  unfold enumerationCoins
  fun_prop









section
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] List.flatMap
noncomputable section




end
end


noncomputable def enumerationCoinProgram (S : SpinLaw) :
    PolyProgram id Nat.bits (enumerationCoins S) :=
  (BooleanLists.packProgram.comp (Poly.program (enumerationCoins_poly S))).congr _ (fun _ => rfl)

noncomputable def exhaustiveRandMachine (S : SpinLaw) : RandMachine :=
  programRandMachine (rawEnumerationOutputProgram S) (enumerationCoinProgram S)

theorem exhaustiveRandMachine_coins {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) :
    (exhaustiveRandMachine S).coins (tupleCode [encInst I, encBin m]) =
      budgetFromPowers ((alphabet S).length ^ N,
        ((alphabet S).length * weightDenominatorBound S) ^ N, m) := by
  change enumerationCoins S _ = _
  rw [enumerationCoins, requestParams_encoded]
  simp only [enumerationBudget, List.map_replicate, naturalProduct_eq,
    List.prod_replicate]

theorem exhaustiveRandMachine_run {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (ω : List Bool) :
    (exhaustiveRandMachine S).run
      (tupleCode [ω, tupleCode [encInst I, encBin m]]) =
        (enumerationSelected S ((instanceListModel I, List.replicate N ()), (m, ω))).flatMap encRat := by
  change rawEnumerationOutput S _ = _
  rw [rawEnumerationOutput, rawEnumerationSelected, requestPair_tupleCode, requestParams_encoded]

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
noncomputable section










































































end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC



theorem samplerRequest_encoded {N : ℕ} (I : Inst N) (m : ℕ) (ω : List Bool) :
    samplerRequest (tupleCode [ω, tupleCode [encInst I, encBin m]]) = encodedSamplerInput I m ω := by
  rw [samplerRequest, requestPair_tupleCode, requestParams_encoded]
  rfl

theorem rawEnumerationOutput_encoded {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (ω : List Bool) :
    rawEnumerationOutput S (tupleCode [ω, tupleCode [encInst I, encBin m]]) =
      (enumerationSelected S ((instanceListModel I, List.replicate N ()), (m, ω))).flatMap encRat := by
  exact exhaustiveRandMachine_run S I m ω





theorem criticalWindowMachine_run_encoded {N : ℕ} (S : SpinLaw) (C : ℕ)
    (I : Inst N) (m : ℕ) (ω : List Bool) :
    (criticalWindowMachine S C).run (tupleCode [ω, tupleCode [encInst I, encBin m]]) =
      if (List.replicate N ()).isEmpty then [] else
        if preInside S C ((instanceListModel I).1, List.replicate N ()) then
          samplerRetryOutput S C (encodedSamplerInput I m ω)
        else (enumerationSelected S ((instanceListModel I, List.replicate N ()), (m, ω))).flatMap encRat := by
  rw [criticalWindowMachine_run_eq, finalSamplerRun, samplerRequest_encoded,
    rawEnumerationOutput_encoded]
  rfl

theorem criticalWindowMachine_coins_encoded {N : ℕ} (S : SpinLaw) (C : ℕ)
    (I : Inst N) (m : ℕ) :
    (criticalWindowMachine S C).coins (tupleCode [encInst I, encBin m]) =
      if (List.replicate N ()).isEmpty then 0 else
        if preInside S C ((instanceListModel I).1, List.replicate N ()) then
          criticalCoins S C (((instanceListModel I).1, List.replicate N ()), m)
        else enumerationBudget S ((instanceListModel I, List.replicate N ()), m) := by
  rw [criticalWindowMachine_coins_eq, finalSamplerCoins, requestParams_encoded]

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section











end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerDataFacts
open CritWinSpin.LocalTM2.Compiled PreprocessPSD







theorem sample_pre {N : ℕ} (I : Inst N) (m F : ℕ) :
    samplerPre (sampleReference I m F) = encodedInput I.1 := rfl

theorem base_eq {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ) :
    baseBudget S C (encodedInput I.1,m) = budgetBase S C I m := by
  simp only [baseBudget,budgetBase,List.length_replicate]
  rfl

theorem radius_eq {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ) :
    samplerR S C (sampleReference I m F) = radius S C I m := by
  change (baseBudget S C (samplerPre (sampleReference I m F),m))^100 = (budgetBase S C I m)^100
  rw [sample_pre,base_eq]

theorem parameters {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ) :
    let D := sampleEulerData S C I m F
    (D.a:ℝ) = 1/(budgetBase S C I m:ℝ) ∧
    (D.dPhi:ℝ) = 1/(radius S C I m:ℝ)^100 ∧
    (D.snap:ℝ) = 1/(radius S C I m:ℝ)^100 ∧
    (D.dRound:ℝ) = 1/(radius S C I m:ℝ)^100 ∧
    (D.sigma:ℝ) = 1/(2048*(radius S C I m:ℝ)^4) ∧
    (D.k:ℝ) = (radius S C I m:ℝ)^100 ∧
    D.sCap = preSelectedLevel S C (encodedInput I.1) ∧
    samplerStepCount S C (sampleReference I m F) = 16*2048^2*(radius S C I m)^12 := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [sampleEulerData,samplerMesh,samplerQuality,samplerStepScale,samplerStepCount,
    radius_eq,sample_pre,base_eq]
  all_goals push_cast
  all_goals try rfl
  have he : (radius S C I m:ℝ)*(radius S C I m:ℝ)*(radius S C I m:ℝ)*(radius S C I m:ℝ) =
      (radius S C I m:ℝ)^4 := by ring
  rw [he]

end CritWinSpin.Implementation.SamplerDataFacts
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerBudgetBounds
open PreprocessIntegral PreprocessPSD

theorem bounds (C N m Q : ℕ) (hC : 2 ≤ C) (hm : 1 ≤ m) :
    let B := C*(N+1)*(m*Q+1)
    let R := B^100
    2^64 ≤ R ∧ N+1 ≤ R ∧ Q ≤ R ∧ 2*C ≤ R ∧ C ≤ R := by
  let B := C*(N+1)*(m*Q+1)
  have hCN : 1 ≤ C*(N+1) := by
    have hh := mul_le_mul (show 1 ≤ C by omega) (show 1 ≤ N+1 by omega) (by decide : 0 ≤ (1:ℕ)) (Nat.zero_le C)
    simpa only [one_mul] using hh
  have hB_CN : C*(N+1) ≤ B := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ m*Q+1 by omega) (Nat.zero_le (C*(N+1)))
    simpa only [mul_one] using hh
  have hB_C : C ≤ B := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ N+1 by omega) (Nat.zero_le C)
    rw [mul_one] at hh
    exact hh.trans hB_CN
  have hB_N : N+1 ≤ B := by
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ C by omega) (Nat.zero_le (N+1))
    rw [one_mul] at hh
    exact hh.trans hB_CN
  have hB_Q : Q ≤ B := by
    have hq := mul_le_mul_of_nonneg_right hm (Nat.zero_le Q)
    rw [one_mul] at hq
    have hh := mul_le_mul_of_nonneg_right hCN (Nat.zero_le (m*Q+1))
    rw [one_mul] at hh
    exact hq.trans ((Nat.le_succ _).trans hh)
  have hB2 : 2 ≤ B := hC.trans hB_C
  have hB1 : 1 ≤ B := by omega
  have hBR : B ≤ B^100 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hB1 (show 1 ≤ (100:ℕ) by decide)
  have hB2R : B^2 ≤ B^100 := Nat.pow_le_pow_right hB1 (by decide)
  have hDouble : 2*C ≤ B^100 := by
    have hh := mul_le_mul_of_nonneg_right hB2 (Nat.zero_le B)
    have hc := mul_le_mul_of_nonneg_left hB_C (show 0 ≤ (2:ℕ) by decide)
    have hi : 2*B ≤ B^2 := by simpa only [pow_two] using hh
    exact hc.trans (hi.trans hB2R)
  have h64 : 2^64 ≤ B^100 := by
    calc
      _ ≤ (2:ℕ)^100 := Nat.pow_le_pow_right (by decide) (by decide)
      _ ≤ _ := pow_le_pow_left₀ (by decide : 0 ≤ (2:ℕ)) hB2 100
  exact ⟨h64,hB_N.trans hBR,hB_Q.trans hBR,hDouble,hB_C.trans hBR⟩

theorem coefficient_le_C (S : SpinLaw) (C : ℕ)
    (hC : 1000*integrationConstant S ≤ (C:ℝ)) : spinErrorCoefficient S ≤ (C:ℝ) := by
  have hH : 1 ≤ (CritWinSpin.LocalTM2.Compiled.fixedScale S:ℝ) := by
    rw [fixedScale_cast]
    nlinarith only [EnvelopeAnalysis.tau_pos S]
  have hK := spinErrorCoefficient_nonneg S
  have hh := mul_le_mul_of_nonneg_right hH hK
  have hI : spinErrorCoefficient S ≤ integrationConstant S := by
    unfold integrationConstant
    nlinarith only [hh,hH,sq_nonneg (CritWinSpin.LocalTM2.Compiled.fixedScale S:ℝ)]
  nlinarith only [hC,hI,hK]

end CritWinSpin.Implementation.SamplerBudgetBounds
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.CriticalAnalyticTrial
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled IsingLTL.BeliefProp
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessIntegral
open SamplerDataFacts DensityAnalysis EnvelopeGeometry ContractiveOperator LangevinBudget

theorem actual_trial_tv {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C : ℕ)
    (I : Inst N) (m F : ℕ) (D : EulerData N) (hD : D = sampleEulerData S C I m F)
    (M0 Ck : ℝ) (hM0 : 0 ≤ M0) (hCk : 0 ≤ Ck)
    (hC : 131072 ≤ C) (hScale : 1000*(fixedScale S : ℝ) ≤ (C : ℝ))
    (hPrecision : 1000*integrationConstant S ≤ (C : ℝ))
    (hM0C : 2048*M0 ≤ (C : ℝ)) (hCkC : 2*Ck ≤ (C : ℝ))
    (hGC : GaussianMoments.sixthConstant ≤ (C : ℝ))
    (hI : I.1.IsSymm) (hm : 5 ≤ m) (hin : preInside S C (encodedInput I.1) = true)
    (hL : ∀ i j, |(D.L i j : ℝ)| ≤ 2*(C : ℝ))
    (hPSD : ((D.sCap : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)-
      castM D.L*(castM D.L).transpose).PosSemidef)
    (hiW : Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S D.sCap (castM D.L) (castV I.2) z)))
    (hiW2 : Integrable (fun z : Fin N → ℝ => normSq z*Real.exp (-Wpot S D.sCap (castM D.L) (castV I.2) z)))
    (hiU : Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S D.sCap D.a (castM D.L) (castV I.2) z)))
    (hMom : (∫ z : Fin N → ℝ, normSq z*normDens (Wpot S D.sCap (castM D.L) (castV I.2)) z) ≤ M0*N)
    (hreg : (1/2 : ℝ)*(∫ z : Fin N → ℝ,
      |normDens (Ualpha S D.sCap D.a (castM D.L) (castV I.2)) z-
        normDens (Wpot S D.sCap (castM D.L) (castV I.2)) z|) ≤ (D.a : ℝ)*M0*N/2)
    (hLip : ∀ z w : Fin N → ℝ,
      tvDist (kernelK S D.sCap (castM D.L) (castV I.2) z)
        (kernelK S D.sCap (castM D.L) (castV I.2) w) ≤
        Ck*Real.sqrt (N : ℝ)*Real.sqrt (normSq (z-w))) :
    tvDist
      (fun v => ∫ z : DensityAnalysis.Point N, SpinKernel.pointKernel S D.sCap (castM D.L) (castV I.2) z v
        ∂D.trajectoryLaw S (samplerStepCount S C (sampleReference I m F)) (0 : Fin N → ℚ))
      (HubbardTrialLaw.law S D.sCap (castM D.L) (castV I.2)) ≤
        1/(2048*((m*trials S C I m+1 : ℕ) : ℝ)) := by
  let Q := trials S C I m
  let B := budgetBase S C I m
  let R := radius S C I m
  let T := samplerStepCount S C (sampleReference I m F)
  have hparams := parameters S C I m F
  rw [← hD] at hparams
  obtain ⟨hA,hPhi,hSnap,hRound,hSigma,hQuality,hCap,hTform⟩ := hparams
  change (D.a : ℝ) = 1/(B : ℝ) at hA
  have hDh : D.h = I.2 := by simp only [hD,sampleEulerData]
  have hBaseReal : EnvelopeParameters.baseBudget (C : ℝ) N ((m : ℝ)*Q) = (B : ℝ) := by
    simp only [EnvelopeParameters.baseBudget,B,budgetBase,Q,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hRadiusCast : (R : ℝ) = (B : ℝ)^100 := by
    simp only [R,radius,B,Nat.cast_pow]
  have hBudgets : 2^64 ≤ R ∧ N+1 ≤ R ∧ Q ≤ R ∧ 2*C ≤ R ∧ C ≤ R := by
    exact SamplerBudgetBounds.bounds C N m Q (by omega) (by omega)
  have hBounds := selected_bounds S C I.1 hI (by omega) hScale hin
  have hs : tau S < (D.sCap : ℝ) := by
    rw [hCap]
    have hbuf : (0 : ℝ) < preBuffer (List.replicate N ()) := by rw [preBuffer_cast]; positivity
    linarith only [hBounds.1,hbuf]
  have hsC : (D.sCap : ℝ) ≤ C := by
    rw [hCap]
    have hf : 0 ≤ (fixedScale S : ℝ) := by exact_mod_cast (fixedScale_pos S).le
    have hfx : (fixedScale S : ℝ) ≤ C := by linarith only [hScale,hf]
    rw [fixedScale_cast] at hfx
    exact hBounds.2.1.trans hfx
  have hiUbase : Integrable (fun z : Fin N → ℝ => Real.exp
      (-Ualpha S D.sCap (1/EnvelopeParameters.baseBudget (C : ℝ) N ((m : ℝ)*Q))
        (castM D.L) (castV I.2) z)) := by
    rw [hBaseReal,← hA]
    exact hiU
  have hSetup : ∃ cert : Certificate N (D.a : ℝ),
      cert.U = potential S D.sCap D.a (castM D.L) (castV I.2) ∧
      cert.g = gradient S D.sCap D.a (castM D.L) (castV I.2) ∧
      0 < (D.a : ℝ) ∧ (D.a : ℝ) ≤ 1 ∧ 2 ≤ (R : ℝ) ∧ 1 ≤ (D.a : ℝ)*R ∧
      (∫ x, ‖x‖ ∂DensityAnalysis.gibbs cert.U) ≤ R ∧
      2+(∫ x, ‖cert.g x‖^6 ∂DensityAnalysis.gibbs cert.U)+
        GaussianMoments.sixthConstant*(N : ℝ)^3 ≤ R ∧
      2*(Ck*Real.sqrt (N : ℝ)) ≤ R ∧
      1/(4*(R : ℝ))+(D.a : ℝ)*M0*N/2 ≤ 1/(2048*((m : ℝ)*Q+1)) := by
    have hh := EnvelopeParameters.setup S hS (castM D.L) (castV I.2)
      hs hsC (mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (Nat.cast_nonneg Q))
      (by exact_mod_cast hC) hM0 hM0C hCk hCkC hGC hPSD hiW hiW2 hiUbase hMom
    dsimp only at hh
    rw [hBaseReal,← hA] at hh
    simpa only [hBaseReal,← hA,← hRadiusCast] using hh
  obtain ⟨cert,hU,hg,ha0,ha1,hR2,haR,hM,hH,hLR,hFinal⟩ := hSetup
  have hRp : (0 : ℝ) < R := by linarith only [hR2]
  have hR1 : (1 : ℝ) ≤ R := by linarith only [hR2]
  have haQ : 0 < D.a := by exact_mod_cast ha0
  have haQ1 : D.a ≤ 1 := by exact_mod_cast ha1
  have hPhi0R : (0 : ℝ) < D.dPhi := by rw [hPhi]; positivity
  have hPhi1R : (D.dPhi : ℝ) ≤ 1 := by
    rw [hPhi]
    exact (div_le_one (by positivity : (0 : ℝ) < (R : ℝ)^100)).mpr (one_le_pow₀ hR1)
  have hPhi0 : 0 < D.dPhi := by exact_mod_cast hPhi0R
  have hPhi1 : D.dPhi ≤ 1 := by exact_mod_cast hPhi1R
  have hSnap0 : 0 < D.snap := by
    have hh : (0 : ℝ) < D.snap := by rw [hSnap]; positivity
    exact_mod_cast hh
  have hRound0 : 0 < D.dRound := by
    have hh : (0 : ℝ) < D.dRound := by rw [hRound]; positivity
    exact_mod_cast hh
  have hSigma0 : 0 < D.sigma := by
    have hh : (0 : ℝ) < D.sigma := by rw [hSigma]; positivity
    exact_mod_cast hh
  have hDimR : (N : ℝ)+1 ≤ R := by exact_mod_cast hBudgets.2.1
  have hEntryR : 2*(C : ℝ) ≤ R := by exact_mod_cast hBudgets.2.2.2.1
  have hCoefR : spinErrorCoefficient S ≤ (R : ℝ) :=
    (SamplerBudgetBounds.coefficient_le_C S C hPrecision).trans (by exact_mod_cast hBudgets.2.2.2.2)
  have hError := EulerFiniteBudget.stepError_budget S D hR2 hDimR
    (by positivity : (0 : ℝ) ≤ 2*C) hEntryR hCoefR hSigma hPhi hSnap hRound hQuality
  have hUeq : cert.U = potential S D.sCap D.a (castM D.L) (castV D.h) := by rw [hDh]; exact hU
  have hGeq : cert.g = gradient S D.sCap D.a (castM D.L) (castV D.h) := by rw [hDh]; exact hg
  have hSteps : 16*(R : ℝ)^4/(D.sigma : ℝ)^2 ≤ (T : ℝ) := by
    rw [hSigma,EulerPrecisionArithmetic.stepCount_formula hRp]
    have hh : (T : ℝ) = 16*2048^2*(R : ℝ)^12 := by
      simpa only [T,R,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
        congrArg (fun n : ℕ => (n : ℝ)) hTform
    rw [hh]
  have hweak (f : DensityAnalysis.Point N → ℝ) (hf : BoundedLip f 1 (2*(Ck*Real.sqrt (N : ℝ)))) :
      |(∫ z, f z ∂D.trajectoryLaw S T (0 : Fin N → ℚ))-
        ∫ z, f z ∂DensityAnalysis.gibbs (potential S D.sCap D.a (castM D.L) (castV I.2))| ≤
          1/(2*(R : ℝ)) := by
    have hh := EulerAnalyticStep.trajectory_weak S hS D hs haQ haQ1 hPSD hPhi0 hPhi1
      hSnap0 hRound0 hSigma0 (2*(C : ℝ)) (by positivity) hL cert hUeq hGeq hR2 haR
      hSigma.le hError hM hH T hSteps f 1 (2*(Ck*Real.sqrt (N : ℝ)))
      (by positivity) hLR hf
    rwa [hDh] at hh
  have hTransfer := EnvelopeKernelTransfer.trial_tv S hS (castM D.L) (castV I.2)
    hs hCk hiW hiU hreg hLip (D.trajectoryLaw S T (0 : Fin N → ℚ)) hweak
  have hFinal' : 1/(4*(R : ℝ))+(D.a : ℝ)*M0*N/2 ≤
      1/(2048*((m*trials S C I m+1 : ℕ) : ℝ)) := by
    simpa only [Q,Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hFinal
  change tvDist
    (fun v => ∫ z : DensityAnalysis.Point N, SpinKernel.pointKernel S D.sCap (castM D.L) (castV I.2) z v
      ∂D.trajectoryLaw S T (0 : Fin N → ℚ))
    (HubbardTrialLaw.law S D.sCap (castM D.L) (castV I.2)) ≤ _
  exact hTransfer.trans ((by ring : (1/(2*(R : ℝ)))/2+(D.a : ℝ)*M0*N/2 =
    1/(4*(R : ℝ))+(D.a : ℝ)*M0*N/2).le.trans hFinal')

end CritWinSpin.Implementation.CriticalAnalyticTrial
end

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CritWinSpin.Implementation.GibbsPerturbation

open IsingLTL.BeliefProp CritWinSpin.LocalTM2

theorem exp_relative_error {u v a : ℝ} (ha : a ≤ 1) (huv : |u - v| ≤ a) :
    |Real.exp u - Real.exp v| ≤ 2 * a * Real.exp v := by
  have hid : Real.exp u - Real.exp v = (Real.exp (u - v) - 1) * Real.exp v := by
    rw [sub_mul, ← Real.exp_add, sub_add_cancel, one_mul]
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos v)]
  exact mul_le_mul_of_nonneg_right
    ((Real.abs_exp_sub_one_le (huv.trans ha)).trans (mul_le_mul_of_nonneg_left huv (by norm_num)))
    (Real.exp_pos v).le

theorem weighted_exp_tv {α : Type} [Fintype α] [Nonempty α]
    (E E' ρ : α → ℝ) (hρ : ∀ x, 0 < ρ x) {a : ℝ}
    (ha : a ≤ 1) (hE : ∀ x, |E' x - E x| ≤ a) :
    tvDist (fun x => Real.exp (E' x) * ρ x / ∑ y, Real.exp (E' y) * ρ y)
      (fun x => Real.exp (E x) * ρ x / ∑ y, Real.exp (E y) * ρ y) ≤ 2 * a := by
  classical
  let w := fun x => Real.exp (E' x) * ρ x
  let f := fun x => Real.exp (E x) * ρ x
  have hwpos : ∀ x, 0 < w x := fun x => mul_pos (Real.exp_pos _) (hρ x)
  have hfpos : ∀ x, 0 < f x := fun x => mul_pos (Real.exp_pos _) (hρ x)
  have hW : 0 < ∑ x, w x := Finset.sum_pos (fun x _ => hwpos x) Finset.univ_nonempty
  have hF : 0 < ∑ x, f x := Finset.sum_pos (fun x _ => hfpos x) Finset.univ_nonempty
  have herr : ∑ x, |w x - f x| ≤ (2 * a) * ∑ x, f x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    change |Real.exp (E' x) * ρ x - Real.exp (E x) * ρ x| ≤ _
    rw [← sub_mul, abs_mul, abs_of_pos (hρ x)]
    have hh := mul_le_mul_of_nonneg_right (exp_relative_error ha (hE x)) (hρ x).le
    simpa only [f, mul_assoc] using hh
  exact (normalize_tv_le f w (fun x => (hwpos x).le) hF hW).trans
    ((div_le_iff₀ hF).2 (by simpa only [mul_comm] using herr))

theorem energy_entry_error {ι : Type} [Fintype ι]
    (J J' : Matrix ι ι ℝ) (h v : ι → ℝ) {e : ℝ}
    (hJ : ∀ i j, |J' i j - J i j| ≤ e) (hv : ∀ i, |v i| ≤ 1) :
    |energy J' h v - energy J h v| ≤ (Fintype.card ι : ℝ) ^ 2 * e / 2 := by
  classical
  have he : energy J' h v - energy J h v =
      (1 / 2) * ∑ i, ∑ j, (J' i j - J i j) * v i * v j := by
    simp only [energy, sub_mul, Finset.sum_sub_distrib]
    ring
  have hp (i j : ι) : |(J' i j - J i j) * v i * v j| ≤ e := by
    rw [abs_mul, abs_mul]
    calc
      |J' i j - J i j| * |v i| * |v j| ≤ |J' i j - J i j| * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)) (hv j)
          (abs_nonneg _) (by positivity)
      _ ≤ e := by simpa using hJ i j
  have hs : |∑ i, ∑ j, (J' i j - J i j) * v i * v j| ≤
      (Fintype.card ι : ℝ) ^ 2 * e := by
    calc
      _ ≤ ∑ i, |∑ j, (J' i j - J i j) * v i * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(J' i j - J i j) * v i * v j| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : ι, ∑ _j : ι, e :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  nlinarith only [hs]

theorem prodRho_pos (S : SpinLaw) {ι : Type} [Fintype ι] (x : Config S ι) :
    0 < prodRho S x := by
  unfold prodRho
  apply Finset.prod_pos
  intro i _
  exact_mod_cast S.pos (x i) (x i).property

theorem spinVal_abs_le (S : SpinLaw) {ι : Type} (x : Config S ι) (i : ι) :
    |spinVal x i| ≤ 1 := by
  have hh := S.mem_Icc (x i) (x i).property
  have hq : |(x i : ℚ)| ≤ 1 := abs_le.mpr hh
  change |((x i : ℚ) : ℝ)| ≤ 1
  exact_mod_cast hq

theorem gibbs_matrix_tv (S : SpinLaw) {ι : Type} [Fintype ι] [DecidableEq ι]
    (J J' : Matrix ι ι ℝ) (h : ι → ℝ) {e : ℝ}
    (hJ : ∀ i j, |J' i j - J i j| ≤ e)
    (hsmall : (Fintype.card ι : ℝ) ^ 2 * e / 2 ≤ 1) :
    tvDist (CritWinSpin.gibbs S J' h) (CritWinSpin.gibbs S J h) ≤
      (Fintype.card ι : ℝ) ^ 2 * e := by
  classical
  letI : Nonempty (Config S ι) := ⟨fun _ => ⟨1, S.one_mem⟩⟩
  have hh := weighted_exp_tv (fun x : Config S ι => energy J h (spinVal x))
    (fun x => energy J' h (spinVal x)) (prodRho S) (prodRho_pos S)
    hsmall (fun x => energy_entry_error J J' h (spinVal x) hJ (spinVal_abs_le S x))
  change tvDist (fun x : Config S ι => gibbsWeight S J' h x / ∑ y, gibbsWeight S J' h y)
    (fun x : Config S ι => gibbsWeight S J h x / ∑ y, gibbsWeight S J h y) ≤ _
  have he : 2 * ((Fintype.card ι : ℝ) ^ 2 * e / 2) = (Fintype.card ι : ℝ) ^ 2 * e := by ring
  rw [he] at hh
  exact hh

theorem option_tv {α : Type} [Fintype α] (p q : α → ℝ) :
    tvDist (fun x : Option α => match x with | none => 0 | some y => p y)
      (fun x : Option α => match x with | none => 0 | some y => q y) = tvDist p q := by
  simp only [tvDist, Fintype.sum_option, sub_self, abs_zero, zero_add]

theorem gibbsOpt_matrix_tv (S : SpinLaw) {ι : Type} [Fintype ι] [DecidableEq ι]
    (J J' : Matrix ι ι ℝ) (h : ι → ℝ) {e : ℝ}
    (hJ : ∀ i j, |J' i j - J i j| ≤ e)
    (hsmall : (Fintype.card ι : ℝ) ^ 2 * e / 2 ≤ 1) :
    tvDist (gibbsOpt S J' h) (gibbsOpt S J h) ≤ (Fintype.card ι : ℝ) ^ 2 * e := by
  unfold tvDist
  simp only [Fintype.sum_option, gibbsOpt, sub_self, abs_zero, zero_add]
  exact gibbs_matrix_tv S J J' h hJ hsmall

end CritWinSpin.Implementation.GibbsPerturbation
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled

theorem tableBits_linear (n m : ℕ) : tableBits (n, m) ≤ 4 * n * m + 1 := by
  unfold tableBits
  change (4 * n * m).size + 1 ≤ 4 * n * m + 1
  have hh : (4 * n * m).size ≤ 4 * n * m := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

theorem gaussian_numeric_bounds (R : ℕ) (hR : 2 ^ 64 ≤ R) :
    gaussianRadius (R ^ 100) ≤ R ^ 101 ∧
      gaussianMeshDen (R ^ 100) ≤ R ^ 401 ∧
      gaussianGridSize (R ^ 100) ≤ R ^ 503 ∧
      gaussianAccuracy (R ^ 100) ≤ R ^ 202 ∧
      gaussianBits (R ^ 100) ≤ R ^ 706 ∧
      gaussianNoiseBits (R ^ 100) ≤ R ^ 1204 := by
  have hR1 : 1 ≤ R := by norm_num at hR ⊢; omega
  have hRbig : 262144 ≤ R := by norm_num at hR; omega
  have hk : 1 ≤ R ^ 100 := one_le_pow₀ hR1
  have hplus : R ^ 100 + 1 ≤ 2 * R ^ 100 := by omega
  have hr : gaussianRadius (R ^ 100) ≤ R ^ 101 := by
    calc
      _ ≤ 32 * R ^ 100 := by unfold gaussianRadius; omega
      _ ≤ R * R ^ 100 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' R 100).symm
  have hd : gaussianMeshDen (R ^ 100) ≤ R ^ 401 := by
    calc
      _ ≤ 16384 * (2 * R ^ 100) ^ 4 := by unfold gaussianMeshDen; gcongr
      _ = 262144 * R ^ 400 := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ R * R ^ 400 := Nat.mul_le_mul_right _ hRbig
      _ = _ := (pow_succ' R 400).symm
  have hg : gaussianGridSize (R ^ 100) ≤ R ^ 503 := by
    calc
      _ ≤ 2 * R ^ 101 * R ^ 401 := by unfold gaussianGridSize; gcongr
      _ = 2 * R ^ 502 := by rw [mul_assoc, ← pow_add]
      _ ≤ R * R ^ 502 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' R 502).symm
  have ha : gaussianAccuracy (R ^ 100) ≤ R ^ 202 := by
    calc
      _ ≤ 64 * R ^ 101 * (2 * R ^ 100) := by unfold gaussianAccuracy; gcongr
      _ = 128 * R ^ 201 := by rw [show 201 = 101 + 100 by decide, pow_add]; ring
      _ ≤ R * R ^ 201 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' R 201).symm
  have hb : gaussianBits (R ^ 100) ≤ R ^ 706 := by
    have hp : 1 ≤ R ^ 705 := one_le_pow₀ hR1
    calc
      _ ≤ 4 * gaussianGridSize (R ^ 100) * gaussianAccuracy (R ^ 100) + 1 := tableBits_linear _ _
      _ ≤ 4 * R ^ 503 * R ^ 202 + 1 := by gcongr
      _ = 4 * R ^ 705 + 1 := by rw [mul_assoc, ← pow_add]
      _ ≤ 5 * R ^ 705 := by omega
      _ ≤ R * R ^ 705 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' R 705).symm
  have hf : gaussianNoiseBits (R ^ 100) ≤ R ^ 1204 := by
    rw [gaussianNoiseBits_budget]
    have hp : 1 ≤ R ^ 1203 := one_le_pow₀ hR1
    have h706 : R ^ 706 ≤ R ^ 1203 := Nat.pow_le_pow_right hR1 (by decide)
    have h503 : R ^ 503 ≤ R ^ 1203 := Nat.pow_le_pow_right hR1 (by decide)
    calc
      _ ≤ R ^ 706 + R ^ 503 + 2 * (R ^ 401) ^ 3 + 2 := by unfold gaussianCoinBudget; gcongr
      _ = R ^ 706 + R ^ 503 + 2 * R ^ 1203 + 2 := by rw [← pow_mul]
      _ ≤ 6 * R ^ 1203 := by omega
      _ ≤ R * R ^ 1203 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' R 1203).symm
  exact ⟨hr, hd, hg, ha, hb, hf⟩

theorem finite_table_bits_budget (R n : ℕ) (hR : 2 ^ 64 ≤ R) (hn : n ≤ R) :
    tableBits (n, R ^ 100 + 1) ≤ R ^ 102 := by
  have hR1 : 1 ≤ R := by norm_num at hR; omega
  have hk : 1 ≤ R ^ 100 := one_le_pow₀ hR1
  have hp : 1 ≤ R ^ 101 := one_le_pow₀ hR1
  calc
    _ ≤ 4 * n * (R ^ 100 + 1) + 1 := tableBits_linear _ _
    _ ≤ 4 * R * (2 * R ^ 100) + 1 := by gcongr <;> omega
    _ = 8 * R ^ 101 + 1 := by rw [pow_succ']; ring
    _ ≤ 9 * R ^ 101 := by omega
    _ ≤ R * R ^ 101 := Nat.mul_le_mul_right _ (by norm_num at hR; omega)
    _ = _ := (pow_succ' R 101).symm

theorem random_fuel_suffices (S : SpinLaw) (R N Q : ℕ) (hR : 2 ^ 64 ≤ R)
    (hN : N ≤ R) (hQ : Q ≤ R) (hA : (alphabet S).length ≤ R) :
    Q * ((16 * 2048 ^ 2 * R ^ 12) * N * gaussianNoiseBits (R ^ 100) +
      acceptanceBits (R ^ 100) + N * spinBits S (R ^ 100)) ≤ R ^ 10000 := by
  have hR1 : 1 ≤ R := by norm_num at hR; omega
  have hstep : 16 * 2048 ^ 2 * R ^ 12 ≤ R ^ 13 := by
    calc
      _ ≤ R * R ^ 12 := Nat.mul_le_mul_right _ (by norm_num at hR ⊢; omega)
      _ = _ := (pow_succ' R 12).symm
  have hnoise := (gaussian_numeric_bounds R hR).2.2.2.2.2
  have hspin : spinBits S (R ^ 100) ≤ R ^ 102 := finite_table_bits_budget R _ hR hA
  have hacc : acceptanceBits (R ^ 100) ≤ R ^ 102 := finite_table_bits_budget R 2 hR (by norm_num at hR; omega)
  have heuler : (16 * 2048 ^ 2 * R ^ 12) * N * gaussianNoiseBits (R ^ 100) ≤ R ^ 1218 := by
    calc
      _ ≤ R ^ 13 * R * R ^ 1204 := by gcongr
      _ = _ := by rw [← pow_succ, ← pow_add]
  have hspins : N * spinBits S (R ^ 100) ≤ R ^ 103 := by
    calc
      _ ≤ R * R ^ 102 := Nat.mul_le_mul hN hspin
      _ = _ := (pow_succ' R 102).symm
  have h103 : R ^ 103 ≤ R ^ 1218 := Nat.pow_le_pow_right hR1 (by decide)
  have h102 : R ^ 102 ≤ R ^ 1218 := Nat.pow_le_pow_right hR1 (by decide)
  have htrial : (16 * 2048 ^ 2 * R ^ 12) * N * gaussianNoiseBits (R ^ 100) +
      acceptanceBits (R ^ 100) + N * spinBits S (R ^ 100) ≤ R ^ 1219 := by
    calc
      _ ≤ 3 * R ^ 1218 := by omega
      _ ≤ R * R ^ 1218 := Nat.mul_le_mul_right _ (by norm_num at hR; omega)
      _ = _ := (pow_succ' R 1218).symm
  calc
    _ ≤ R * R ^ 1219 := Nat.mul_le_mul hQ htrial
    _ = R ^ 1220 := (pow_succ' R 1219).symm
    _ ≤ _ := Nat.pow_le_pow_right hR1 (by decide)

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled

theorem gaussianMeshDen_ge_square (k : ℕ) : (k + 1) ^ 2 ≤ gaussianMeshDen k := by
  have hp : (k + 1) ^ 2 ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold gaussianMeshDen
  nlinarith

theorem gaussianNoiseBits_exp_fuel (k : ℕ) :
    2 * (gaussianMeshDen k) ^ 3 + 2 ≤ gaussianNoiseBits k := by
  rw [gaussianNoiseBits_budget]
  unfold gaussianCoinBudget
  omega

theorem gaussianNoiseBits_linear (k : ℕ) : 8 * (k + 1) ≤ gaussianNoiseBits k := by
  have hden : 4 * (k + 1) ≤ gaussianMeshDen k := by
    have hp : k + 1 ≤ (k + 1) ^ 4 := Nat.le_self_pow (by decide) _
    unfold gaussianMeshDen
    nlinarith
  have hden1 : 1 ≤ gaussianMeshDen k := by omega
  have hp : gaussianMeshDen k ≤ (gaussianMeshDen k) ^ 3 := Nat.le_self_pow (by decide) _
  have hh := gaussianNoiseBits_exp_fuel k
  omega

theorem reciprocal_exp_fuel (k D F : ℕ) (hD : 0 < D)
    (hDk : D ≤ gaussianMeshDen k) (hF : gaussianNoiseBits k ≤ F) :
    2 / (((1 / (D : ℚ) : ℚ) : ℝ) ^ 3) + 2 ≤ (F : ℝ) := by
  have hdR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have he : 2 / (((1 / (D : ℚ) : ℚ) : ℝ) ^ 3) + 2 = ((2 * D ^ 3 + 2 : ℕ) : ℝ) := by
    push_cast
    field_simp [hdR]
  rw [he]
  exact_mod_cast le_trans (show 2 * D ^ 3 + 2 ≤ 2 * (gaussianMeshDen k) ^ 3 + 2 from by gcongr)
    ((gaussianNoiseBits_exp_fuel k).trans hF)

theorem global_gaussian_fuel (R : ℕ) (hR : 2 ^ 64 ≤ R) :
    gaussianNoiseBits (R ^ 100) ≤ R ^ 10000 :=
  (gaussian_numeric_bounds R hR).2.2.2.2.2.trans
    (Nat.pow_le_pow_right (by norm_num at hR; omega) (by decide))

theorem spin_exp_fuel (C R : ℕ) (hR : 2 ^ 64 ≤ R) (hC : 0 < C) (hCR : C ≤ R) :
    2 / (spinPrecision C (R ^ 100) : ℝ) ^ 3 + 2 ≤ (R ^ 10000 : ℕ) := by
  have hR1 : 1 ≤ R := by norm_num at hR; omega
  have hC4 : C ^ 4 ≤ R ^ 100 := (Nat.pow_le_pow_left hCR 4).trans
    (Nat.pow_le_pow_right hR1 (by decide))
  have hd : C ^ 4 * (R ^ 100 + 1) ≤ gaussianMeshDen (R ^ 100) := by
    calc
      _ ≤ (R ^ 100 + 1) * (R ^ 100 + 1) := by gcongr; omega
      _ = (R ^ 100 + 1) ^ 2 := (pow_two _).symm
      _ ≤ _ := gaussianMeshDen_ge_square _
  have he := reciprocal_exp_fuel (R ^ 100) (C ^ 4 * (R ^ 100 + 1)) (R ^ 10000)
    (by positivity) hd (global_gaussian_fuel R hR)
  simpa only [spinPrecision, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast, Rat.cast_add] using he

theorem drift_exp_fuel (R : ℕ) (hR : 2 ^ 64 ≤ R) :
    2 / (((1 / (R ^ 100 : ℚ) : ℚ) : ℝ) ^ 3) + 2 ≤ (R ^ 10000 : ℕ) := by
  have hR1 : 1 ≤ R := by norm_num at hR; omega
  have hk : 0 < R ^ 100 := by positivity
  have hd : R ^ 100 ≤ gaussianMeshDen (R ^ 100) := by
    have hh := gaussianMeshDen_ge_square (R ^ 100)
    nlinarith
  have he := reciprocal_exp_fuel (R ^ 100) (R ^ 100) (R ^ 10000) hk hd (global_gaussian_fuel R hR)
  simpa only [Nat.cast_pow] using he

theorem integral_exp_fuel (R : ℕ) (hR : 2 ^ 64 ≤ R) :
    2 / (((1 / ((R ^ 100 : ℕ) + 1 : ℚ) : ℚ) : ℝ) ^ 3) + 2 ≤ (R ^ 10000 : ℕ) := by
  have hd : R ^ 100 + 1 ≤ gaussianMeshDen (R ^ 100) := by
    have hh := gaussianMeshDen_ge_square (R ^ 100)
    nlinarith
  have he := reciprocal_exp_fuel (R ^ 100) (R ^ 100 + 1) (R ^ 10000) (by omega) hd
    (global_gaussian_fuel R hR)
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using he

theorem root_denominator_budget (C m N R : ℕ) (hR : 2 ^ 64 ≤ R)
    (hCR : C ≤ R) (hmR : m ≤ R) (hNR : N ≤ R) :
    C ^ 4 * m * (N + 1) ^ 3 ≤ R ^ 100 := by
  have hR1 : 1 ≤ R := by norm_num at hR; omega
  have hR2 : 2 ≤ R := by norm_num at hR; omega
  have hN : N + 1 ≤ R ^ 2 := by nlinarith
  calc
    _ ≤ R ^ 4 * R * (R ^ 2) ^ 3 := by gcongr
    _ = R ^ 11 := by rw [← pow_mul, ← pow_succ, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hR1 (by decide)

theorem root_precision_fuel (C m N R : ℕ) (hR : 2 ^ 64 ≤ R)
    (hC : 0 < C) (hm : 0 < m) (hCR : C ≤ R) (hmR : m ≤ R) (hNR : N ≤ R) :
    8 ≤ ((1 / ((C : ℚ) ^ 4 * (m : ℚ) * ((N : ℚ) + 1) ^ 3) : ℚ) : ℝ) *
      ((R ^ 10000 : ℕ) + 2 : ℝ) := by
  let D := C ^ 4 * m * (N + 1) ^ 3
  have hD : 0 < D := by dsimp [D]; positivity
  have hd := root_denominator_budget C m N R hR hCR hmR hNR
  have hf := (gaussianNoiseBits_linear (R ^ 100)).trans (global_gaussian_fuel R hR)
  have hF : 8 * D ≤ R ^ 10000 + 2 := by dsimp only [D]; omega
  have hcast : (1 / ((C : ℚ) ^ 4 * (m : ℚ) * ((N : ℚ) + 1) ^ 3) : ℚ) = 1 / (D : ℚ) := by
    dsimp [D]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [hcast]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  have hp : (0 : ℝ) < D := by exact_mod_cast hD
  calc
    8 ≤ ((R ^ 10000 : ℕ) + 2 : ℝ) / (D : ℝ) :=
      (le_div_iff₀ hp).mpr (by exact_mod_cast hF)
    _ = _ := by ring

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.LocalTM2.Compiled.SamplerMatrixCertificate
open Matrix IsingLTL.BeliefProp
open CritWinSpin.Implementation PreprocessPSD PreprocessSelection PreprocessBranches





theorem covariance_psd {N : ℕ} (C : ℕ) (I : Inst N) (m F : ℕ) :
    (covariance C I m F).PosSemidef := by
  simpa only [covariance,Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (castM (sampleRootMatrix C I m F))

theorem root_symmetric {N : ℕ} (C : ℕ) (I : Inst N) (m F : ℕ) (hI : I.1.IsSymm) :
    (sampleRootMatrix C I m F).IsSymm := by
  unfold sampleRootMatrix
  exact (roundedMatrixSqrt_symm _ (hI.smul _) _ F).smul _

theorem root_entry_bound {N : ℕ} (C : ℕ) (I : Inst N) (m F : ℕ) (i j : Fin N) :
    |castM (sampleRootMatrix C I m F) i j| ≤ 2 * (C : ℝ) := by
  unfold sampleRootMatrix
  rw [castM_smulQ]
  simp only [Matrix.smul_apply, smul_eq_mul, Rat.cast_natCast, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
  have hh := roundedMatrixSqrt_entry_bound ((1 / ((C : ℚ)*C)) • I.1)
    (rootTolerance ((List.replicate N (),List.replicate F ()),rootTarget C N m)) F i j
  dsimp only [rootTarget] at hh
  nlinarith only [hh,Nat.cast_nonneg (α := ℝ) C]

theorem root_residual {N : ℕ} (C : ℕ) (I : Inst N) (m F : ℕ)
    (hC : 0 < C) (hm : 0 < m) (hI : I.1.IsSymm)
    (hPSD : (castM I.1).PosSemidef)
    (hTop : ((C : ℝ)^2 • (1 : Matrix (Fin N) (Fin N) ℝ)-castM I.1).PosSemidef)
    (hFuelRoot : (8 : ℝ) ≤ (rootTarget C N m : ℝ) * ((F : ℝ)+2)) :
    ∀ i j, |(covariance C I m F-castM I.1) i j| ≤ rootError C N m := by
  let A : Matrix (Fin N) (Fin N) ℚ := (1 / ((C : ℚ)*C)) • I.1
  let eta := rootTarget C N m
  let d := rootTolerance ((List.replicate N (),List.replicate F ()),eta)
  let Y := castM (roundedMatrixSqrt A d F)
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNP : (0 : ℝ) < (N : ℝ)+1 := by positivity
  have heta : (0 : ℚ) < eta := by dsimp [eta,rootTarget]; positivity
  have hAcast : castM A = (1 / ((C : ℝ)*C)) • castM I.1 := by
    dsimp only [A]
    rw [castM_smulQ]
    simp only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_natCast]
  have hA : (castM A).PosSemidef := by rw [hAcast]; exact hPSD.smul (by positivity)
  have hA1 : ((1 : Matrix (Fin N) (Fin N) ℝ)-castM A).PosSemidef := by
    have hh := hTop.smul (by positivity : (0 : ℝ) ≤ 1 / ((C : ℝ)*C))
    have he : (1 / ((C : ℝ)*C)) • ((C : ℝ)^2 • (1 : Matrix (Fin N) (Fin N) ℝ)-castM I.1) =
        1-castM A := by
      rw [hAcast]
      ext i j
      simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
      field_simp
      <;> ring
    rwa [he] at hh
  have hASym : A.IsSymm := hI.smul _
  have hYSym : Y.IsSymm := Matrix.isHermitian_iff_isSymm.mp
    (castM_symm _ (roundedMatrixSqrt_symm A hASym d F))
  have htest := approximatePSDTest_complete A hA hA1 eta heta (List.replicate F ())
    (by simpa only [List.length_replicate] using hFuelRoot)
  have hresQ : ∀ i j, |(A-(roundedMatrixSqrt A d F)^2) i j| ≤ eta := by
    have hh := (approximatePSDTest_spec A d eta (List.replicate F ())).mp htest
    simpa only [List.length_replicate] using hh
  have hres (i j : Fin N) : |(castM A-Y^2) i j| ≤ (eta : ℝ) := by
    have hc : castM (A-(roundedMatrixSqrt A d F)^2) = castM A-Y^2 := by
      rw [castM_subQ,pow_two,pow_two,castM_mulQ]
    rw [← hc]
    change |((A-(roundedMatrixSqrt A d F)^2) i j : ℝ)| ≤ (eta : ℝ)
    exact_mod_cast hresQ i j
  have hL : castM (sampleRootMatrix C I m F) = (C : ℝ) • Y := by
    rw [sampleRootMatrix,castM_smulQ]
    rfl
  have hCov : covariance C I m F = (C : ℝ)^2 • Y^2 := by
    rw [covariance,hL,Matrix.transpose_smul,hYSym.eq,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    simp only [pow_two]
  have hid : castM I.1-covariance C I m F = (C : ℝ)^2 • (castM A-Y^2) := by
    rw [hCov,hAcast]
    ext i j
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    field_simp
    <;> ring
  have heq : (C : ℝ)^2 * (eta : ℝ) = rootError C N m := by
    simp only [eta,rootTarget,rootError,Rat.cast_div,Rat.cast_one,Rat.cast_mul,
      Rat.cast_pow,Rat.cast_natCast,Rat.cast_add]
    field_simp
    <;> ring
  intro i j
  rw [Matrix.sub_apply,abs_sub_comm]
  change |(castM I.1-covariance C I m F) i j| ≤ _
  rw [hid,Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (sq_nonneg (C : ℝ))]
  exact (mul_le_mul_of_nonneg_left (hres i j) (sq_nonneg (C : ℝ))).trans_eq heq

theorem error_gibbs_budget (C N m : ℕ) (hC : 8 ≤ C) (hm : 1 ≤ m) :
    (N : ℝ)^2 * rootError C N m ≤ 1 / (64 * (m : ℝ)) := by
  have hC8 : (8 : ℝ) ≤ C := by exact_mod_cast hC
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hCpos : (0 : ℝ) < C := by linarith only [hC8]
  have hmpos : (0 : ℝ) < m := by linarith only [hm1]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hC2 : (64 : ℝ) ≤ (C : ℝ)^2 := by nlinarith only [hC8,sq_nonneg ((C : ℝ)-8)]
  have hN3 : (N : ℝ)^2 ≤ ((N : ℝ)+1)^3 := by nlinarith [pow_nonneg hN0 3]
  have hp := mul_le_mul hC2 hN3 (sq_nonneg (N : ℝ)) (sq_nonneg (C : ℝ))
  simp only [rootError,mul_one_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < 64*m)]
  nlinarith only [mul_le_mul_of_nonneg_right hp hmpos.le]

theorem error_spectral_budget (C N m : ℕ) (hC : (1000 : ℝ) ≤ C) (hm : 1 ≤ m) :
    (N : ℝ)^2 * rootError C N m ≤ (preBuffer (List.replicate N ()) : ℝ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hCpos : (0 : ℝ) < C := by linarith only [hC]
  have hmpos : (0 : ℝ) < m := by linarith only [hm1]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hC2 : (1000 : ℝ) ≤ (C : ℝ)^2 := by nlinarith only [hC,sq_nonneg ((C : ℝ)-1)]
  have hCm : (1000 : ℝ) ≤ (C : ℝ)^2 * m := by
    simpa only [mul_one] using mul_le_mul hC2 hm1 zero_le_one (sq_nonneg (C : ℝ))
  have hN2 : (N : ℝ)^2 ≤ ((N : ℝ)+1)^2 := by nlinarith only [hN0]
  have hp := mul_le_mul hCm hN2 (sq_nonneg (N : ℝ))
    (mul_nonneg (sq_nonneg (C : ℝ)) hmpos.le)
  rw [preBuffer_cast]
  simp only [rootError,mul_one_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < 1000*((N : ℝ)+1))]
  nlinarith only [mul_le_mul_of_nonneg_right hp (show (0 : ℝ) ≤ (N : ℝ)+1 by positivity)]

theorem actual_root_certificate {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ)
    (hI : I.1.IsSymm) (hPSD : (castM I.1).PosSemidef) (hC8 : 8 ≤ C)
    (hScale : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ))
    (hin : preInside S C (encodedInput I.1) = true) (hm : 5 ≤ m)
    (hFuelRoot : (8 : ℝ) ≤ (rootTarget C N m : ℝ) * ((F : ℝ)+2)) :
    (sampleRootMatrix C I m F).IsSymm ∧
    (∀ i j, |castM (sampleRootMatrix C I m F) i j| ≤ 2*(C : ℝ)) ∧
    (∀ i j, |(covariance C I m F-castM I.1) i j| ≤ rootError C N m) ∧
    (covariance C I m F).PosSemidef ∧
    (((sampleEulerData S C I m F).sCap : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)-covariance C I m F).PosSemidef ∧
    tvDist (gibbsOpt S (covariance C I m F) (castV I.2))
      (gibbsOpt S (castM I.1) (castV I.2)) ≤ 1 / (64*(m : ℝ)) := by
  have hm1 : 1 ≤ m := by omega
  have hCR : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hfixed : 1 ≤ (fixedScale S : ℝ) := by
    rw [fixedScale_cast]
    linarith only [(EnvelopeAnalysis.tau_pos S).le]
  have hC1000 : (1000 : ℝ) ≤ C := by linarith only [hScale,hfixed]
  have hCupper : (fixedScale S : ℝ) ≤ (C : ℝ)^2 := by
    nlinarith only [hScale,hfixed,hCR.le,sq_nonneg ((C : ℝ)-1)]
  have hb := selected_bounds S C I.1 hI hC8 hScale hin
  have hbuf : (0 : ℝ) ≤ preBuffer (List.replicate N ()) := by rw [preBuffer_cast]; positivity
  have hupper : ((C : ℝ)^2 • (1 : Matrix (Fin N) (Fin N) ℝ)-castM I.1).PosSemidef :=
    scalar_shift_mono _ (by rw [fixedScale_cast] at hCupper; linarith only [hb.2.1,hCupper,hbuf]) hb.2.2
  have hres := root_residual C I m F (by omega) (by omega) hI hPSD hupper hFuelRoot
  have he0 : 0 ≤ rootError C N m := by unfold rootError; positivity
  have hcov := covariance_psd C I m F
  have herr : (castM I.1-covariance C I m F + ((N : ℝ)^2*rootError C N m) •
      (1 : Matrix (Fin N) (Fin N) ℝ)).PosSemidef := by
    apply positive_up_to_entry_error _ ((castM_symm I.1 hI).sub hcov.isHermitian) _ he0
    intro i j
    simpa only [Matrix.sub_apply,abs_sub_comm] using hres i j
  have hadd := hb.2.2.add herr
  have hid : ((preSelectedLevel S C (encodedInput I.1) : ℝ)-(preBuffer (List.replicate N ()) : ℝ)) •
      (1 : Matrix (Fin N) (Fin N) ℝ)-castM I.1 +
      (castM I.1-covariance C I m F + ((N : ℝ)^2*rootError C N m) • 1) =
      ((preSelectedLevel S C (encodedInput I.1) : ℝ)-(preBuffer (List.replicate N ()) : ℝ)+
        (N : ℝ)^2*rootError C N m) • 1-covariance C I m F := by
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  rw [hid] at hadd
  have hbudget := error_spectral_budget C N m hC1000 hm1
  have hcovUpper : ((preSelectedLevel S C (encodedInput I.1) : ℝ) •
      (1 : Matrix (Fin N) (Fin N) ℝ)-covariance C I m F).PosSemidef :=
    scalar_shift_mono _ (by linarith only [hbudget]) hadd
  have hgBudget := error_gibbs_budget C N m hC8 hm1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hsmall : (Fintype.card (Fin N) : ℝ)^2 * rootError C N m / 2 ≤ 1 := by
    simp only [Fintype.card_fin]
    have h1 : 1 / (64*(m : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hmR])
    linarith only [hgBudget,h1]
  have htv := GibbsPerturbation.gibbsOpt_matrix_tv S (castM I.1) (covariance C I m F) (castV I.2) hres hsmall
  refine ⟨root_symmetric C I m F hI,root_entry_bound C I m F,hres,hcov,?_,?_⟩
  · exact hcovUpper
  · have htv' : tvDist (gibbsOpt S (covariance C I m F) (castV I.2))
        (gibbsOpt S (castM I.1) (castV I.2)) ≤ (N : ℝ)^2 * rootError C N m := by
      simpa only [Fintype.card_fin] using htv
    exact htv'.trans hgBudget

theorem actual_root_fuel {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 2 ≤ C) (hm : 1 ≤ m) :
    (8 : ℝ) ≤ (rootTarget C N m : ℝ) *
      ((criticalCoins S C (encodedInput I.1,m) : ℝ)+2) := by
  let Q := retryCount S C (encodedInput I.1,m)
  let B := C*(N+1)*(m*Q+1)
  let R := B^100
  have hpow : 1 ≤ boundedPower 4 (polynomialFuel C 1 (List.replicate N ()),
      preCap S C (encodedInput I.1)) := by
    simp only [boundedPower,naturalProduct_eq,List.map_const',List.prod_replicate]
    exact one_le_pow₀ (by decide)
  have hQ : m ≤ Q := by
    dsimp only [Q,retryCount]
    exact (show m ≤ 16*m by omega).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hb : 2^64 ≤ R ∧ N+1 ≤ R ∧ Q ≤ R ∧ 2*C ≤ R ∧ C ≤ R := by
    exact SamplerBudgetBounds.bounds C N m Q hC hm
  have hF : criticalCoins S C (encodedInput I.1,m) = R^10000 := by
    dsimp only [R,B]
    rw [criticalCoins,uniformBudget,baseBudget]
    simp only [encodedInput,List.length_replicate,Q]
  rw [hF]
  exact root_precision_fuel C m N R hb.1 (by omega) (by omega) hb.2.2.2.2
    (hQ.trans hb.2.2.1) ((Nat.le_succ N).trans hb.2.1)

theorem sampler_matrix_certificate {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hI : I.1.IsSymm) (hPSD : (castM I.1).PosSemidef) (hC8 : 8 ≤ C)
    (hScale : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ))
    (hin : preInside S C (encodedInput I.1) = true) (hm : 5 ≤ m) :
    let F := criticalCoins S C (encodedInput I.1,m)
    (sampleRootMatrix C I m F).IsSymm ∧
    (∀ i j, |castM (sampleRootMatrix C I m F) i j| ≤ 2*(C : ℝ)) ∧
    (∀ i j, |(covariance C I m F-castM I.1) i j| ≤ rootError C N m) ∧
    (covariance C I m F).PosSemidef ∧
    (((sampleEulerData S C I m F).sCap : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)-covariance C I m F).PosSemidef ∧
    tvDist (gibbsOpt S (covariance C I m F) (castV I.2))
      (gibbsOpt S (castM I.1) (castV I.2)) ≤ 1 / (64*(m : ℝ)) := by
  exact actual_root_certificate S C I m _ hI hPSD hC8 hScale hin hm
    (actual_root_fuel S C I m (by omega) (by omega))

end CritWinSpin.LocalTM2.Compiled.SamplerMatrixCertificate
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessCap
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessIntegral

theorem discrepancy_zero_le (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) :
    ds S s 0 ≤ s := by
  have hsp := (EnvelopeAnalysis.tau_pos S).trans hs
  have hOutside := EnvelopeIntegral.discrepancy_outside S s s
    (show asOf S s ≤ |s| by rw [abs_of_nonneg hsp.le]; exact EnvelopeIntegral.asOf_le_s S hS hs)
  have hh := EnvelopeAnalysis.ds_sub_le S hS hs 0 s
  rw [hOutside] at hh
  simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hsp.le] at hh
  exact (le_abs_self _).trans hh

theorem preCap_bounds {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hC : 8 ≤ C)
    (hPrecision : 1000 * integrationConstant S ≤ (C : ℝ))
    (hs : tau S < (preSelectedLevel S C (encodedInput J) : ℝ))
    (hu : (preSelectedLevel S C (encodedInput J) : ℝ) ≤ 2 * tau S + 1) :
    (N : ℝ) * ds S (preSelectedLevel S C (encodedInput J)) 0 ≤ (preCap S C (encodedInput J) : ℝ) ∧
      (preCap S C (encodedInput J) : ℝ) ≤ (N : ℝ) * ds S (preSelectedLevel S C (encodedInput J)) 0 + 2 := by
  let s := preSelectedLevel S C (encodedInput J)
  let b : ℝ := preBuffer (List.replicate N ())
  let v : ℝ := preIntegral S C (encodedInput J)
  let x : ℝ := (N : ℝ) * (v+b)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hErr := preIntegral_error S hS C J hC hPrecision hs hu
  change |v - ds S (s:ℝ) 0| ≤ b at hErr
  have hlow : ds S (s:ℝ) 0 ≤ v+b := by linarith only [(abs_le.mp hErr).1]
  have hhigh : v ≤ ds S (s:ℝ) 0 + b := by linarith only [(abs_le.mp hErr).2]
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg hN ((EnvelopeAnalysis.ds_nonneg S hS hs 0).trans hlow)
  have hCap : (preCap S C (encodedInput J) : ℝ) = 1 + (⌊x⌋₊ : ℝ) := by
    simp only [preCap, rationalFloor_real, List.length_replicate, Nat.cast_add, Nat.cast_one]
    push_cast
    rfl
  have hf := Nat.floor_le hx
  have hflt := Nat.lt_floor_add_one x
  have hsmall : 2 * (N : ℝ) * b ≤ 1 := by
    dsimp only [b]
    rw [preBuffer_cast]
    have he : 2 * (N : ℝ) * (1/(1000*((N:ℝ)+1))) =
        (2*(N:ℝ))/(1000*((N:ℝ)+1)) := by ring
    rw [he]
    apply (div_le_one (by positivity : (0:ℝ) < 1000*((N:ℝ)+1))).2
    nlinarith only [hN]
  have hxlow : (N : ℝ) * ds S (s:ℝ) 0 ≤ x := mul_le_mul_of_nonneg_left hlow hN
  have hxhigh : x ≤ (N : ℝ) * ds S (s:ℝ) 0 + 2*(N:ℝ)*b := by
    have hh := mul_le_mul_of_nonneg_left hhigh hN
    dsimp only [x]
    nlinarith only [hh]
  constructor
  · linarith only [hxlow, hflt, hCap]
  · linarith only [hf, hCap, hxhigh, hsmall]

theorem cap_fits_fuel {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hJ : J.IsSymm) (hC8 : 8 ≤ C)
    (hC : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ))
    (hPrecision : 1000 * integrationConstant S ≤ (C : ℝ))
    (hin : preInside S C (encodedInput J) = true) :
    preCap S C (encodedInput J) ≤ C * (N+1) := by
  have hb := selected_bounds S C J hJ hC8 hC hin
  have hbuf : (0 : ℝ) < preBuffer (List.replicate N ()) := by rw [preBuffer_cast]; positivity
  have hs : tau S < (preSelectedLevel S C (encodedInput J) : ℝ) := by linarith only [hb.1, hbuf]
  have hcap := (preCap_bounds S hS C J hC8 hPrecision hs hb.2.1).2
  have hds := discrepancy_zero_le S hS hs
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hMul := mul_le_mul_of_nonneg_left hds hN
  have hMulS := mul_le_mul_of_nonneg_left hb.2.1 hN
  have hH : 1 ≤ (fixedScale S : ℝ) := by rw [fixedScale_cast]; nlinarith only [EnvelopeAnalysis.tau_pos S]
  have hcH : (fixedScale S : ℝ) ≤ (C : ℝ) := by nlinarith only [hC, hH]
  have hc2 : (2 : ℝ) ≤ C := by exact_mod_cast (show 2 ≤ C by omega)
  have hh := mul_le_mul_of_nonneg_right hcH hN
  rw [fixedScale_cast] at hh
  have hFloat : (preCap S C (encodedInput J) : ℝ) ≤ (C : ℝ) * ((N : ℝ)+1) := by
    nlinarith only [hcap, hMul, hMulS, hh, hc2]
  exact_mod_cast hFloat

theorem retryCount_formula {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C m : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hJ : J.IsSymm) (hC8 : 8 ≤ C)
    (hC : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ))
    (hPrecision : 1000 * integrationConstant S ≤ (C : ℝ))
    (hin : preInside S C (encodedInput J) = true) :
    retryCount S C (encodedInput J,m) = 16 * m * 4 ^ preCap S C (encodedInput J) := by
  have hf := cap_fits_fuel S hS C J hJ hC8 hC hPrecision hin
  have hfuel : preCap S C (encodedInput J) ≤ (polynomialFuel C 1 (List.replicate N ())).length := by
    rw [polynomialFuel_length, List.length_replicate, pow_one]
    exact hf
  unfold retryCount
  rw [boundedPower_correct 4 _ _ hfuel]

end CritWinSpin.Implementation.PreprocessCap
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.KernelPrecisionBudget
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessIntegral



theorem table_loose (n k : ℕ) : (n:ℝ)/(2:ℝ)^tableBits (n,k+1) ≤ 1/((k:ℝ)+1) := by
  have hh := tableRounding_error_bound n (k+1) (by omega)
  have hl : 1/(4*((k:ℝ)+1)) ≤ 1/((k:ℝ)+1) :=
    one_div_le_one_div_of_le (by positivity) (by have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k; nlinarith only [hk])
  norm_num only [Nat.cast_add,Nat.cast_one] at hh
  exact hh.trans hl

theorem error_le {R : ℝ} (S : SpinLaw) (C N k : ℕ) (s : ℝ)
    (hR : 2 ≤ R) (hC : 1 ≤ C) (hCR : (C:ℝ) ≤ R) (hNR : (N:ℝ)+1 ≤ R)
    (hs0 : 0 ≤ s) (hsC : s ≤ C) (hKC : spinErrorCoefficient S ≤ C)
    (hqC : (alphabet S).length ≤ C) (hInv : 1/(S.ρ 1:ℝ) ≤ C) :
    error S C N k s ≤ 8*R^3/((k:ℝ)+1) := by
  have hRp : 0 < R := by linarith only [hR]
  have hR1 : 1 ≤ R := by linarith only [hR]
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hNR' : (N:ℝ) ≤ R := by linarith only [hNR]
  have hC1 : (1:ℝ) ≤ C := by exact_mod_cast hC
  have hCp : (0:ℝ) < C := by linarith only [hC1]
  have hρ : (0:ℝ) < S.ρ 1 := by exact_mod_cast S.pos 1 S.one_mem
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hq : ((alphabet S).length:ℝ) ≤ C := by exact_mod_cast hqC
  have hK0 := spinErrorCoefficient_nonneg S
  have hF : s^2+s+spinErrorCoefficient S*s ≤ 3*R^2 := by
    have h₂ := pow_le_pow_left₀ hs0 hsC 2
    have h₃ := mul_le_mul hKC hsC hs0 hCp.le
    have hC2 : (C:ℝ) ≤ (C:ℝ)^2 := by nlinarith only [hC1,sq_nonneg ((C:ℝ)-1)]
    have hR2 := pow_le_pow_left₀ hCp.le hCR 2
    nlinarith only [h₂,h₃,hC2,hR2,hsC]
  have hF0 : 0 ≤ s^2+s+spinErrorCoefficient S*s := by positivity
  have hNF : (N:ℝ)*(s^2+s+spinErrorCoefficient S*s) ≤ 3*R^3 := by
    have hh := mul_le_mul hNR' hF hF0 hRp.le
    nlinarith only [hh]
  have hacc : 4/(2:ℝ)^acceptanceBits k ≤ 2/((k:ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_left (table_loose 2 k) (show (0:ℝ) ≤ 2 by norm_num)
    norm_num only [Nat.cast_ofNat] at hh
    change 2*((2:ℝ)/(2:ℝ)^acceptanceBits k) ≤ 2*(1/((k:ℝ)+1)) at hh
    convert hh using 1 <;> ring
  have hspinQ : ((alphabet S).length:ℝ)/(2:ℝ)^spinBits S k ≤ 1/((k:ℝ)+1) :=
    table_loose (alphabet S).length k
  have hratio : ((alphabet S).length:ℝ)/(S.ρ 1:ℝ) ≤ (C:ℝ)^4 := by
    have hh := mul_le_mul hq hInv (by positivity : 0 ≤ 1/(S.ρ 1:ℝ)) hCp.le
    have h24 : (C:ℝ)^2 ≤ (C:ℝ)^4 := pow_le_pow_right₀ hC1 (by decide)
    have hr : ((alphabet S).length:ℝ)/(S.ρ 1:ℝ) ≤ (C:ℝ)^2 := by
      calc
        _ = ((alphabet S).length:ℝ)*(1/(S.ρ 1:ℝ)) := by ring
        _ ≤ (C:ℝ)*(C:ℝ) := hh
        _ = _ := by ring
    exact hr.trans h24
  have hspinW : ((alphabet S).length:ℝ)*(spinPrecision C k:ℝ)/(S.ρ 1:ℝ) ≤ 1/((k:ℝ)+1) := by
    have hd : (spinPrecision C k:ℝ) = 1/((C:ℝ)^4*((k:ℝ)+1)) := by simp [spinPrecision]
    rw [hd]
    have he : ((alphabet S).length:ℝ)*(1/((C:ℝ)^4*((k:ℝ)+1)))/(S.ρ 1:ℝ) =
        (((alphabet S).length:ℝ)/(S.ρ 1:ℝ))/((C:ℝ)^4*((k:ℝ)+1)) := by ring
    rw [he]
    have hh := div_le_div_of_nonneg_right hratio (by positivity : 0 ≤ (C:ℝ)^4*((k:ℝ)+1))
    have hz : (C:ℝ)^4/((C:ℝ)^4*((k:ℝ)+1)) = 1/((k:ℝ)+1) := by field_simp [hCp.ne',hk.ne']
    exact hh.trans_eq hz
  have hspins := mul_le_mul_of_nonneg_left (add_le_add hspinW hspinQ) hN0
  have hR3 : 1 ≤ R^3 := one_le_pow₀ hR1
  have hRto3 : R ≤ R^3 := by simpa only [pow_one] using pow_le_pow_right₀ hR1 (show 1 ≤ (3:ℕ) by decide)
  have hNto3 : (N:ℝ) ≤ R^3 := hNR'.trans hRto3
  have hNum : 3+(N:ℝ)*(s^2+s+spinErrorCoefficient S*s)+2*(N:ℝ) ≤ 8*R^3 := by
    nlinarith only [hNF,hR3,hNto3]
  unfold error
  calc
    _ ≤ (1+(N:ℝ)*(s^2+s+spinErrorCoefficient S*s))/((k:ℝ)+1)+
        2/((k:ℝ)+1)+(N:ℝ)*(1/((k:ℝ)+1)+1/((k:ℝ)+1)) :=
      add_le_add (add_le_add le_rfl hacc) hspins
    _ = (3+(N:ℝ)*(s^2+s+spinErrorCoefficient S*s)+2*(N:ℝ))/((k:ℝ)+1) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hNum hk.le

theorem high_precision_bound {R y : ℝ} (hR : 2 ≤ R) (hy : 0 < y) (hyR : y ≤ R) :
    8*R^3/(R^100+1) ≤ 1/(2048*y) := by
  have hRp : 0 < R := by linarith only [hR]
  have h96 : (16384:ℝ) ≤ R^96 :=
    (by norm_num : (16384:ℝ) ≤ (2:ℝ)^96).trans
      (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hR 96)
  have hh := mul_le_mul_of_nonneg_left h96 (pow_nonneg hRp.le 4)
  have hFirst : 8*R^3/(R^100+1) ≤ 1/(2048*R) := by
    apply (div_le_div_iff₀ (by positivity : 0 < R^100+1) (by positivity : 0 < 2048*R)).2
    nlinarith only [hh]
  exact hFirst.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith only [hyR]))

theorem actual_kernel_budget (S : SpinLaw) (C N R : ℕ) (s y : ℝ)
    (hR : 2 ≤ R) (hC : 1 ≤ C) (hCR : (C:ℝ) ≤ R) (hNR : (N:ℝ)+1 ≤ R)
    (hs0 : 0 ≤ s) (hsC : s ≤ C) (hKC : spinErrorCoefficient S ≤ C)
    (hqC : (alphabet S).length ≤ C) (hInv : 1/(S.ρ 1:ℝ) ≤ C)
    (hy : 0 < y) (hyR : y ≤ R) :
    error S C N (R^100) s ≤ 1/(2048*y) := by
  have hr : (2:ℝ) ≤ R := by exact_mod_cast hR
  have hh := error_le S C N (R^100) s hr hC hCR hNR hs0 hsC hKC hqC hInv
  push_cast at hh
  exact hh.trans (high_precision_bound hr hy hyR)

theorem accuracyProduct_le_radius (C N m Q : ℕ) (hC : 1 ≤ C) :
    m*Q+1 ≤ (C*(N+1)*(m*Q+1))^100 := by
  have hCN : 1 ≤ C*(N+1) := by
    have hh := mul_le_mul_of_nonneg_right hC (Nat.zero_le (N+1))
    rw [one_mul] at hh
    omega
  have hh := mul_le_mul_of_nonneg_right hCN (Nat.zero_le (m*Q+1))
  rw [one_mul] at hh
  have hB : 1 ≤ C*(N+1)*(m*Q+1) := by omega
  have hp : C*(N+1)*(m*Q+1) ≤ (C*(N+1)*(m*Q+1))^100 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hB (show 1 ≤ (100:ℕ) by decide)
  exact hh.trans hp

end CritWinSpin.Implementation.KernelPrecisionBudget
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness
open Classical IsingLTL.BeliefProp MeasureTheory
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.Implementation PreprocessPSD PreprocessIntegral SamplerDataFacts
noncomputable section

theorem inside_tv_core {N : ℕ} (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) (C : ℕ)
    (I : Inst N) (m F : ℕ) (D : EulerData N)
    (r : Option (Config S (Fin N)) → ℝ) (hr : IsDistribution r)
    (hF : F = criticalCoins S C (encodedInput I.1,m)) (hD : D = sampleEulerData S C I m F)
    (M0 Ck : ℝ) (hM0 : 0   ≤   M0) (hCk : 0   ≤   Ck)
    (hC : 131072   ≤   C) (hScale : 1000*(fixedScale S:ℝ)   ≤   (C:ℝ))
    (hPrecision : 1000*integrationConstant S   ≤   (C:ℝ))
    (hM0C : 2048*M0   ≤   (C:ℝ)) (hCkC : 2*Ck   ≤   (C:ℝ))
    (hGC : GaussianMoments.sixthConstant   ≤   (C:ℝ))
    (hqC : (alphabet S).length   ≤   C) (hInv : 1/(S.ρ 1:ℝ)   ≤   (C:ℝ))
    (hN : 0 < N) (hI : I.1.IsSymm) (hJPSD : (castM I.1).PosSemidef)
    (hm : 5  ≤  m) (hin : preInside S C (encodedInput I.1) = true)
    (hiW : Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S D.sCap (castM D.L) (castV I.2) z)))
    (hiW2 : Integrable (fun z : Fin N → ℝ => normSq z*Real.exp (-Wpot S D.sCap (castM D.L) (castV I.2) z)))
    (hiU : Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S D.sCap D.a (castM D.L) (castV I.2) z)))
    (hMom : (∫ z : Fin N → ℝ, normSq z*normDens (Wpot S D.sCap (castM D.L) (castV I.2)) z)   ≤   M0*N)
    (hreg : (1/2:ℝ)*(∫ z : Fin N → ℝ,
      |normDens (Ualpha S D.sCap D.a (castM D.L) (castV I.2)) z-
        normDens (Wpot S D.sCap (castM D.L) (castV I.2)) z|)   ≤   (D.a:ℝ)*M0*N/2)
    (hLip : ∀ z w : Fin N → ℝ,
      tvDist (kernelK S D.sCap (castM D.L) (castV I.2) z)
        (kernelK S D.sCap (castM D.L) (castV I.2) w)   ≤  
        Ck*Real.sqrt (N:ℝ)*Real.sqrt (normSq (z-w)))
    (hnum : tvDist r (fun x => ∫ z, SpinKernel.pointKernel S D.sCap (castM D.L) (castV I.2) z x
      ∂D.trajectoryLaw S (samplerStepCount S C (sampleReference I m F)) (fun _ => 0)) ≤
        KernelPrecisionBudget.error S C N D.k D.sCap)
    (hwordlaw : outLaw (criticalWindowMachine S C) (tupleCode [encInst I,encBin m]) (decConfig S N) =
      FiniteRetry.retry r (trials S C I m)) :
    tvDist (outLaw (criticalWindowMachine S C) (tupleCode [encInst I,encBin m]) (decConfig S N))
      (gibbsOpt S (castM I.1) (castV I.2))   ≤   1/(m:ℝ) := by
  subst F
  subst D
  let F := criticalCoins S C (encodedInput I.1,m)
  let D := sampleEulerData S C I m F
  let Q := trials S C I m
  let R := radius S C I m
  let T := samplerStepCount S C (sampleReference I m F)
  let Jhat := castM D.L * (castM D.L).transpose
  have hC2 : 2  ≤  C := by omega
  have hC8 : 8  ≤  C := by omega
  have hm1 : 1  ≤  m := by omega
  have hmR : 0  <  (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hparams := parameters S C I m F
  have hDc : D.sCap = preSelectedLevel S C (encodedInput I.1) := hparams.2.2.2.2.2.2.1
  have hDh : D.h = I.2 := rfl
  have hk : D.k = R^100 := by simp only [D,sampleEulerData,samplerQuality,radius_eq,R]
  have hbounds := PreprocessBranches.selected_bounds S C I.1 hI hC8 hScale hin
  have hs : tau S  <  (D.sCap:ℝ) := by
    rw [hDc]
    have hb : (0:ℝ) < preBuffer (List.replicate N ()) := by rw [PreprocessSelection.preBuffer_cast]; positivity
    linarith only [hbounds.1,hb]
  have hsupper : (D.sCap:ℝ)  ≤  2*tau S+1 := by rw [hDc]; exact hbounds.2.1
  have hsC : (D.sCap:ℝ)  ≤  C := by
    have hf : 0  ≤  (fixedScale S:ℝ) := by exact_mod_cast (fixedScale_pos S).le
    have hh : (fixedScale S:ℝ)  ≤  C := by linarith only [hScale,hf]
    rw [fixedScale_cast] at hh
    exact hsupper.trans hh
  have hs0 : 0  ≤  (D.sCap:ℝ) := ((EnvelopeAnalysis.tau_pos S).trans hs).le
  have hmatrix := SamplerMatrixCertificate.sampler_matrix_certificate S C I m hI hJPSD hC8 hScale hin hm
  have hL : ∀ i j, |(D.L i j:ℝ)|  ≤  2*(C:ℝ) := hmatrix.2.1
  have hJhatPSD : Jhat.PosSemidef := hmatrix.2.2.2.1
  have hPSD : ((D.sCap:ℝ) • (1:Matrix (Fin N) (Fin N) ℝ)-Jhat).PosSemidef := hmatrix.2.2.2.2.1
  have hmatrixTV : tvDist (gibbsOpt S Jhat (castV I.2))
      (gibbsOpt S (castM I.1) (castV I.2))  ≤  1/(64*(m:ℝ)) := hmatrix.2.2.2.2.2
  have hb : 2^64  ≤  R ∧ N+1  ≤  R ∧ Q  ≤  R ∧ 2*C  ≤  R ∧ C  ≤  R :=
    SamplerBudgetBounds.bounds C N m Q hC2 hm1
  have hR2 : 2 ≤ R := by norm_num at hb; omega
  have hNR : (N:ℝ)+1  ≤  R := by exact_mod_cast hb.2.1
  have hCR : (C:ℝ)  ≤  R := by exact_mod_cast hb.2.2.2.2
  have hyR : (((m*Q+1:ℕ):ℝ))  ≤  R := by
    exact_mod_cast KernelPrecisionBudget.accuracyProduct_le_radius C N m Q (by omega)
  have hy : (0:ℝ) < ((m*Q+1:ℕ):ℝ) := by positivity
  have hnumBudget := KernelPrecisionBudget.actual_kernel_budget S C N R (D.sCap:ℝ)
    (((m*Q+1:ℕ):ℝ)) hR2 (by omega) hCR hNR hs0 hsC
    (SamplerBudgetBounds.coefficient_le_C S C hPrecision) hqC hInv hy hyR
  rw [hk] at hnum
  have hnum' := hnum.trans hnumBudget
  have hanal := CriticalAnalyticTrial.actual_trial_tv S hS C I m F D rfl M0 Ck hM0 hCk
    hC hScale hPrecision hM0C hCkC hGC hI hm hin hL hPSD hiW hiW2 hiU hMom hreg hLip
  have htrial : tvDist (r) (HubbardTrialLaw.law S D.sCap (castM D.L) (castV I.2))  ≤ 
      1/(1024*((m*Q+1:ℕ):ℝ)) := by
    have ht := FiniteRetry.tv_triangle (r)
      (fun v => ∫ z, SpinKernel.pointKernel S D.sCap (castM D.L) (castV I.2) z v
        ∂D.trajectoryLaw S T (fun _ => 0)) (HubbardTrialLaw.law S D.sCap (castM D.L) (castV I.2))
    have he : 1/(2048*((m*Q+1:ℕ):ℝ))+1/(2048*((m*Q+1:ℕ):ℝ)) =
      1/(1024*((m*Q+1:ℕ):ℝ)) := by ring
    exact (ht.trans (add_le_add hnum' hanal)).trans_eq he
  obtain ⟨α,hα,hα1,hαlow,hHS⟩ := HubbardTrialLaw.ideal_trial S p hS hp Jhat (castM D.L) (castV I.2)
    hs hJhatPSD rfl hiW
  rw [hHS] at htrial
  let cap := preCap S C (encodedInput I.1)
  have hcaps := PreprocessCap.preCap_bounds S hS C I.1 hC8 hPrecision (by rw [←hDc]; exact hs)
    (by rw [←hDc]; exact hsupper)
  have hαcap : Real.exp (-(cap:ℝ))  ≤  α := by
    have hh : (N:ℝ)*ds S D.sCap 0  ≤  (cap:ℝ) := by rw [hDc]; exact hcaps.1
    exact (Real.exp_le_exp.mpr (neg_le_neg hh)).trans hαlow
  have hQformula : Q=16*m*4^cap := PreprocessCap.retryCount_formula S hS C m I.1 hI hC8 hScale hPrecision hin
  have hQpos : 0 < Q := by rw [hQformula]; positivity
  have hQposR : (0:ℝ) < Q := by exact_mod_cast hQpos
  have hQcast : (Q:ℝ)=16*(m:ℝ)*(4:ℝ)^cap := by exact_mod_cast hQformula
  have hretryCount : 16*(m:ℝ)  ≤  α*(Q:ℝ) := by
    rw [hQcast]
    exact HubbardTrialLaw.retry_budget m cap hαcap
  have hε : 1/(1024*((m*Q+1:ℕ):ℝ))  ≤  1/(64*(m:ℝ)*(Q:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    nlinarith only [mul_nonneg hmR.le hQposR.le]
  have hπ : IsDistribution (CritWinSpin.gibbs S Jhat (castV I.2)) := by
    letI : Nonempty (Config S (Fin N)) := ⟨fun _ => ⟨1,S.one_mem⟩⟩
    have hw (x : Config S (Fin N)) : 0 < gibbsWeight S Jhat (castV I.2) x := by
      unfold gibbsWeight prodRho
      exact mul_pos (Real.exp_pos _) (Finset.prod_pos (fun i _ => by exact_mod_cast S.pos (x i).1 (x i).2))
    have hZ := Finset.sum_pos (fun x (_ : x ∈ Finset.univ) => hw x) Finset.univ_nonempty
    constructor
    · intro x; exact div_nonneg (hw x).le hZ.le
    · unfold CritWinSpin.gibbs
      rw [←Finset.sum_div,div_self hZ.ne']
  have hretry := FiniteRetry.retry_error_budget hπ hα.le hα1 hr htrial Q hmR hretryCount hε
  have hlift : FiniteRetry.lift (CritWinSpin.gibbs S Jhat (castV I.2)) =
      gibbsOpt S Jhat (castV I.2) := by
    funext x
    cases x <;> rfl
  rw [hlift] at hretry
  rw [hwordlaw]
  have ht := FiniteRetry.tv_triangle (FiniteRetry.retry (r) Q)
    (gibbsOpt S Jhat (castV I.2)) (gibbsOpt S (castM I.1) (castV I.2))
  have hsum : 1/(8*(m:ℝ))+1/(64*(m:ℝ))  ≤  1/(m:ℝ) := by
    field_simp [hmR.ne'] <;> nlinarith only [hmR]
  exact ht.trans ((add_le_add hretry hmatrixTV).trans hsum)

end
end CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CritWinSpin.Implementation.FiniteRetry
open IsingLTL.BeliefProp
variable {A : Type} [Fintype A]



def wordMass (r : Option A → ℝ) {q : ℕ} (xs : Fin q → Option A) : ℝ := ∏ i, r (xs i)

open Classical in
def wordLaw (r : Option A → ℝ) (q : ℕ) (z : Option A) : ℝ :=
  ∑ xs : Fin q → Option A, if firstSome xs = z then wordMass r xs else 0

theorem wordMass_sum {r : Option A → ℝ} (hr : IsDistribution r) (q : ℕ) :
    ∑ xs : Fin q → Option A, wordMass r xs = 1 := by
  simp only [wordMass, ← Fintype.prod_sum, hr.2, Finset.prod_const_one]

theorem wordLaw_eq_retry {r : Option A → ℝ} (hr : IsDistribution r) (q : ℕ) (z : Option A) :
    wordLaw r q z = retry r q z := by
  classical
  induction q generalizing z with
  | zero => cases z <;> simp [wordLaw, firstSome, wordMass, retry]
  | succ q ih =>
    unfold wordLaw
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (q + 1) => Option A))
      (fun xs : Fin (q + 1) → Option A => if firstSome xs = z then wordMass r xs else 0)]
    simp only [Fintype.sum_prod_type]
    rw [Fintype.sum_option]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, firstSome, Fin.cons_zero, Fin.cons_succ,
      wordMass, Fin.prod_univ_succ]
    have hn : (∑ xs : Fin q → Option A,
        if firstSome xs = z then r none * ∏ i, r (xs i) else 0) = r none * retry r q z := by
      rw [← ih z]
      unfold wordLaw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xs _
      split_ifs <;> simp [wordMass]
    rw [hn]
    have hs (a : A) : (∑ xs : Fin q → Option A,
        if some a = z then r (some a) * ∏ i, r (xs i) else 0) =
        if some a = z then r (some a) else 0 := by
      split_ifs with ha
      · rw [← Finset.mul_sum]
        have hh := wordMass_sum hr q
        change (∑ xs : Fin q → Option A, ∏ i, r (xs i)) = 1 at hh
        rw [hh, mul_one]
      · simp
    simp_rw [hs]
    cases z with
    | none => simp [retry, next]
    | some z => simp [retry, next]; ring

end CritWinSpin.Implementation.FiniteRetry
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.RetryPacketDecoding
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

theorem encRat_nonempty (q : ℚ) : encRat q ≠ [] := by
  unfold encRat encInt
  split_ifs <;> simp

theorem encConfig_nonempty {S : SpinLaw} {N : ℕ} (hN : 0 < N) (x : Config S (Fin N)) : encConfig x ≠ [] := by
  cases N with
  | zero => omega
  | succ n =>
    simp only [encConfig,List.ofFn_succ,List.flatten_cons]
    intro hh
    exact encRat_nonempty _ (List.append_eq_nil_iff.mp hh).1

theorem decConfig_nil (S : SpinLaw) (N : ℕ) (hN : 0 < N) : decConfig S N [] = none := by
  classical
  unfold decConfig
  split_ifs with h
  · obtain ⟨x,hx⟩ := h
    exact False.elim (encConfig_nonempty hN x hx)
  · rfl

def packet {S : SpinLaw} {N : ℕ} : Option (Config S (Fin N)) → List Bool
  | none => []
  | some x => encConfig x

























end CritWinSpin.Implementation.RetryPacketDecoding
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

theorem abs_four (a b c d : ℚ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  exact (abs_add_le (a + b + c) d).trans
    (add_le_add ((abs_add_le (a + b) c).trans
      (add_le_add (abs_add_le a b) le_rfl)) le_rfl)

def coordinateIncrement {N : ℕ} (D : EulerData N) (C : ℚ) : ℚ :=
  2 * C ^ 2 * N + gaussianRadius D.k + 3

theorem coordinateIncrement_nonneg {N : ℕ} (D : EulerData N) (C : ℚ) :
    0 ≤ coordinateIncrement D C := by unfold coordinateIncrement; positivity

theorem EulerData.next_growth {N : ℕ} (D : EulerData N) (S : SpinLaw) (C : ℚ)
    (hC : 0 ≤ C) (ha : 0 ≤ D.a) (ha1 : D.a ≤ 1)
    (hσ : 0 ≤ D.sigma) (hσ1 : D.sigma ≤ 1) (hσ2 : 2 * D.sigma ^ 2 ≤ 1)
    (hsnap : 0 < D.snap) (hsnap1 : D.snap ≤ 1)
    (hround : 0 < D.dRound) (hround1 : D.dRound ≤ 1)
    (hL : ∀ i j, |D.L i j| ≤ 2 * C)
    (hcoeff : ∀ t : ℚ, |modifiedDerivativeApprox S D.sCap t D.dPhi| ≤ C)
    (z : Fin N → ℚ) (ω : Fin (N * gaussianNoiseBits D.k) → Bool) (i : Fin N) :
    |D.next S z ω i| ≤ |z i| + coordinateIncrement D C := by
  let snapped : Fin N → ℚ := fun j => roundTowardZero (z j, D.snap)
  let q : Fin N → ℚ := fun j => modifiedDerivativeApprox S D.sCap
    (D.L.mulVec snapped j + D.h j) D.dPhi
  let r : ℚ := ∑ j, D.L j i * q j
  let G : ℚ := gaussianDraw (D.k, List.ofFn (fun j => ω (blockIndex i j)))
  have hr : |r| ≤ 2 * C ^ 2 * N := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      (∑ j, |D.L j i * q j|) ≤ ∑ _j : Fin N, (2 * C) * C := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hL j i) (hcoeff _) (abs_nonneg _) (by positivity)
      _ = _ := by simp; ring
  have hG : |G| ≤ gaussianRadius D.k := by exact_mod_cast gaussianDraw_bound D.k _
  have hsn : |z i - snapped i| ≤ 1 := by
    have hh := (roundTowardZero_error (z i) D.snap hsnap).trans hsnap1
    simpa only [abs_sub_comm] using hh
  have hbase : 0 ≤ 1 - D.sigma ^ 2 * (1 + D.a) ∧
      1 - D.sigma ^ 2 * (1 + D.a) ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg D.sigma]
  have hσsq : 0 ≤ D.sigma ^ 2 ∧ D.sigma ^ 2 ≤ 1 := ⟨sq_nonneg _, by nlinarith⟩
  have hfac : 0 ≤ D.sigma ^ 2 * (1 + D.a) ∧ D.sigma ^ 2 * (1 + D.a) ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg D.sigma]
  have hAplus : 0 ≤ 1 + D.a := by linarith
  have hb1 : (1 - D.sigma ^ 2 * (1 + D.a)) * |z i| ≤ |z i| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hbase.2 (abs_nonneg (z i))
  have hb2 := mul_le_mul hfac.2 hsn (abs_nonneg (z i - snapped i)) (by norm_num : (0 : ℚ) ≤ 2)
  have hb3 := mul_le_mul hσsq.2 hr (abs_nonneg r) (by norm_num : (0 : ℚ) ≤ 1)
  have hb4 := mul_le_mul hσ1 hG (abs_nonneg G) (by norm_num : (0 : ℚ) ≤ 1)
  have hid : D.raw S z ω i = (1 - D.sigma ^ 2 * (1 + D.a)) * z i +
      D.sigma ^ 2 * (1 + D.a) * (z i - snapped i) + D.sigma ^ 2 * r + D.sigma * G := by
    simp only [EulerData.raw, approximateGradient]
    change _ = (1 - D.sigma ^ 2 * (1 + D.a)) * z i +
      D.sigma ^ 2 * (1 + D.a) * (z i - snapped i) + D.sigma ^ 2 * r + D.sigma * G
    dsimp only [r, q, snapped, G]
    ring
  have hraw : |D.raw S z ω i| ≤ |z i| + 2 * C ^ 2 * N + gaussianRadius D.k + 2 := by
    rw [hid]
    calc
      _ ≤ |(1 - D.sigma ^ 2 * (1 + D.a)) * z i| +
          |D.sigma ^ 2 * (1 + D.a) * (z i - snapped i)| +
          |D.sigma ^ 2 * r| + |D.sigma * G| := by
        exact abs_four ((1 - D.sigma ^ 2 * (1 + D.a)) * z i)
          (D.sigma ^ 2 * (1 + D.a) * (z i - snapped i)) (D.sigma ^ 2 * r) (D.sigma * G)
      _ ≤ |z i| + 2 * 1 + 1 * (2 * C ^ 2 * N) + 1 * gaussianRadius D.k := by
        simp only [abs_mul, abs_of_nonneg hbase.1, abs_of_nonneg hfac.1,
          abs_of_nonneg hσsq.1, abs_of_nonneg hσ, abs_of_nonneg hAplus]
        exact add_le_add (add_le_add (add_le_add hb1 hb2) hb3) hb4
      _ = _ := by ring
  have he := roundTowardZero_error (D.raw S z ω i) D.dRound hround
  have ht := abs_add_le (D.next S z ω i - D.raw S z ω i) (D.raw S z ω i)
  rw [sub_add_cancel] at ht
  change |D.next S z ω i - D.raw S z ω i| ≤ D.dRound at he
  dsimp only [coordinateIncrement]
  linarith

theorem EulerData.capped_fold_eq {N : ℕ} (D : EulerData N) (S : SpinLaw) (C : ℚ)
    (hC : 0 ≤ C) (ha : 0 ≤ D.a) (ha1 : D.a ≤ 1)
    (hσ : 0 ≤ D.sigma) (hσ1 : D.sigma ≤ 1) (hσ2 : 2 * D.sigma ^ 2 ≤ 1)
    (hsnap : 0 < D.snap) (hsnap1 : D.snap ≤ 1)
    (hround : 0 < D.dRound) (hround1 : D.dRound ≤ 1)
    (hL : ∀ i j, |D.L i j| ≤ 2 * C)
    (hcoeff : ∀ t : ℚ, |modifiedDerivativeApprox S D.sCap t D.dPhi| ≤ C)
    (F : ℕ) (hbound : D.bound = 1 + (F : ℚ) * coordinateIncrement D C)
    (words : List (Fin (N * gaussianNoiseBits D.k) → Bool)) (n : ℕ)
    (hn : n + words.length ≤ F) (z : Fin N → ℚ)
    (hz : ∀ i, |z i| ≤ (n : ℚ) * coordinateIncrement D C) :
    words.foldl (D.cappedNext S) z = words.foldl (D.next S) z := by
  have hinc := coordinateIncrement_nonneg D C
  have hB : 0 < D.bound := by rw [hbound]; positivity
  induction words generalizing n z with
  | nil => rfl
  | cons w words ih =>
      have hnext : ∀ i, |D.next S z w i| ≤ ((n + 1 : ℕ) : ℚ) * coordinateIncrement D C := by
        intro i
        have hh := D.next_growth S C hC ha ha1 hσ hσ1 hσ2 hsnap hsnap1 hround hround1 hL hcoeff z w i
        push_cast
        nlinarith [hz i]
      have hsmall : ∀ i, |D.next S z w i| ≤ 2 * D.bound := by
        intro i
        have hn1 : n + 1 ≤ F := by simp only [List.length_cons] at hn; omega
        have hnQ : ((n + 1 : ℕ) : ℚ) ≤ F := by exact_mod_cast hn1
        have hm := mul_le_mul_of_nonneg_right hnQ hinc
        rw [hbound]
        linarith [hnext i]
      have he := D.cappedNext_eq_next S hB z w hsmall
      simp only [List.foldl_cons, he]
      exact ih (n + 1) (by simp only [List.length_cons] at hn; omega) (D.next S z w) hnext

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.LocalTM2.Compiled.SamplerCappedPath
open CritWinSpin.Implementation PreprocessPSD PreprocessSelection PreprocessBranches

 theorem coins_eq_radius {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ) :
    criticalCoins S C (encodedInput I.1,m) = (SamplerDataFacts.radius S C I m)^10000 := by
  simp only [criticalCoins,uniformBudget,SamplerDataFacts.radius,SamplerDataFacts.base_eq]

 theorem stepCount_le_coins {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 2 ≤ C) (hm : 1 ≤ m) :
    samplerStepCount S C (sampleReference I m (criticalCoins S C (encodedInput I.1,m))) ≤
      criticalCoins S C (encodedInput I.1,m) := by
  let R := SamplerDataFacts.radius S C I m
  have hb := SamplerBudgetBounds.bounds C N m (SamplerDataFacts.trials S C I m) hC hm
  change 2^64 ≤ R ∧ _ at hb
  have hR1 : 1 ≤ R := by omega
  have hc : 16*2048^2 ≤ R := by norm_num at hb; omega
  have ht := (SamplerDataFacts.parameters S C I m (criticalCoins S C (encodedInput I.1,m))).2.2.2.2.2.2.2
  rw [ht,coins_eq_radius]
  change 16*2048^2*R^12 ≤ R^10000
  calc
    _ ≤ R*R^12 := Nat.mul_le_mul_right _ hc
    _ = R^13 := by ring
    _ ≤ _ := Nat.pow_le_pow_right hR1 (by decide)

 theorem data_bound {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ) :
    (sampleEulerData S C I m F).bound =
      1+(F:ℚ)*coordinateIncrement (sampleEulerData S C I m F) C := by
  simp only [sampleEulerData,samplerStateBound,coordinateIncrement,
    sampleReference,encodedSamplerInput,instanceListModel,List.length_replicate,List.length_ofFn]
  ring

 theorem actual_capped_fold_eq {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 131072 ≤ C) (hScale : 1000*(fixedScale S:ℝ) ≤ (C:ℝ))
    (hPrecision : 1000*PreprocessIntegral.integrationConstant S ≤ (C:ℝ))
    (hI : I.1.IsSymm) (hin : preInside S C (encodedInput I.1) = true) (hm : 5 ≤ m) :
    let F := criticalCoins S C (encodedInput I.1,m)
    let D := sampleEulerData S C I m F
    ∀ words : List (Fin (N*gaussianNoiseBits D.k) → Bool),
      words.length ≤ samplerStepCount S C (sampleReference I m F) →
      words.foldl (D.cappedNext S) (fun _ => 0) =
        words.foldl (D.next S) (fun _ => 0) := by
  dsimp only
  let F := criticalCoins S C (encodedInput I.1,m)
  let D := sampleEulerData S C I m F
  let B := SamplerDataFacts.budgetBase S C I m
  let R := SamplerDataFacts.radius S C I m
  have hC2 : 2 ≤ C := by omega
  have hm1 : 1 ≤ m := by omega
  have hb := SamplerBudgetBounds.bounds C N m (SamplerDataFacts.trials S C I m) hC2 hm1
  change 2^64 ≤ R ∧ N+1 ≤ R ∧ SamplerDataFacts.trials S C I m ≤ R ∧ 2*C ≤ R ∧ C ≤ R at hb
  have hR1 : 1 ≤ R := by omega
  have hR2Q : (2:ℚ) ≤ R := by exact_mod_cast (show 2 ≤ R by omega)
  have hR1Q : (1:ℚ) ≤ R := by linarith
  have hRpQ : (1:ℚ) ≤ (R:ℚ)^100 := one_le_pow₀ hR1Q
  have hRpR : (R:ℝ) ≤ (R:ℝ)^100 := by exact_mod_cast (Nat.le_self_pow (by decide : 100 ≠ 0) R)
  have hB : 2 ≤ B := by
    calc
      _ ≤ C := hC2
      _ ≤ C*(N+1) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ B := Nat.le_mul_of_pos_right _ (by omega)
  have hB1Q : (1:ℚ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  obtain ⟨hA,hPhi,hSnap,hRound,hSigma,hK,hCap,hT⟩ := SamplerDataFacts.parameters S C I m F
  have hAq : D.a = 1/(B:ℚ) := by
    change 1/(baseBudget S C (samplerPre (sampleReference I m F),m):ℚ) = _
    rw [SamplerDataFacts.sample_pre,SamplerDataFacts.base_eq]
  have hPhiq : D.dPhi = 1/(R:ℚ)^100 := by
    change samplerMesh S C (sampleReference I m F) = _
    simp only [samplerMesh,samplerQuality,SamplerDataFacts.radius_eq,Nat.cast_pow]
    rfl
  have hSnapq : D.snap = 1/(R:ℚ)^100 := hPhiq
  have hRoundq : D.dRound = 1/(R:ℚ)^100 := hPhiq
  have hSigmaq : D.sigma = 1/(2048*(R:ℚ)^4) := by
    change samplerStepScale S C (sampleReference I m F) = _
    simp only [samplerStepScale,SamplerDataFacts.radius_eq]
    congr 1
    ring
  have ha : 0 ≤ D.a := by rw [hAq]; positivity
  have ha1 : D.a ≤ 1 := by rw [hAq]; simpa only [div_one] using one_div_le_one_div_of_le (by norm_num) hB1Q
  have hmesh : 0 < (1:ℚ)/(R:ℚ)^100 ∧ (1:ℚ)/(R:ℚ)^100 ≤ 1 := by
    constructor
    · positivity
    · simpa only [div_one] using one_div_le_one_div_of_le (by norm_num) hRpQ
  have hsigden : (2:ℚ) ≤ 2048*(R:ℚ)^4 := by nlinarith [one_le_pow₀ hR1Q (n := 4)]
  have hsig0 : 0 ≤ D.sigma := by rw [hSigmaq]; positivity
  have hsigHalf : D.sigma ≤ 1/2 := by rw [hSigmaq]; exact one_div_le_one_div_of_le (by norm_num) hsigden
  have hsigma : D.sigma ≤ 1 := by linarith
  have hsigma2 : 2*D.sigma^2 ≤ 1 := by nlinarith
  have hL : ∀ i j, |D.L i j| ≤ 2*(C:ℚ) := by
    intro i j
    have hh := SamplerMatrixCertificate.root_entry_bound C I m F i j
    change |((sampleRootMatrix C I m F) i j:ℝ)| ≤ 2*(C:ℝ) at hh
    change |(sampleRootMatrix C I m F) i j| ≤ 2*(C:ℚ)
    exact_mod_cast hh
  have hcap : tau S < (D.sCap:ℝ) := by
    have hh := selected_bounds S C I.1 hI (by omega) hScale hin
    have hbuf : (0:ℝ) < (preBuffer (List.replicate N ()):ℝ) := by rw [preBuffer_cast]; positivity
    change D.sCap = _ at hCap
    rw [hCap]
    linarith only [hh.1,hbuf]
  have hcoeff : ∀ t : ℚ, |modifiedDerivativeApprox S D.sCap t D.dPhi| ≤ (C:ℚ) := by
    intro t
    have hd : 0 < D.dPhi := by rw [hPhiq]; exact hmesh.1
    have hd1 : D.dPhi ≤ 1 := by rw [hPhiq]; exact hmesh.2
    have hh := modifiedDerivativeApprox_bound S hS D.sCap t D.dPhi hcap hd hd1
    have hco := SamplerBudgetBounds.coefficient_le_C S C hPrecision
    have hcoR : PreprocessIntegral.spinErrorCoefficient S ≤ (R:ℝ)^100 :=
      (hco.trans (by exact_mod_cast hb.2.2.2.2)).trans hRpR
    have hden : (0:ℝ) < (R:ℝ)^100 := by positivity
    have hratio : PreprocessIntegral.spinErrorCoefficient S*(D.dPhi:ℝ) ≤ 1 := by
      have he : PreprocessIntegral.spinErrorCoefficient S*(D.dPhi:ℝ) =
          PreprocessIntegral.spinErrorCoefficient S/(R:ℝ)^100 := by
        rw [hPhi]
        ring
      rw [he]
      exact (div_le_one hden).mpr hcoR
    have hrewrite : 2*(Fintype.card {a:ℚ // a∈S.A}:ℝ)*(D.dPhi:ℝ)/(S.ρ 1:ℝ) =
        PreprocessIntegral.spinErrorCoefficient S*(D.dPhi:ℝ) := by
      unfold PreprocessIntegral.spinErrorCoefficient
      ring
    rw [hrewrite] at hh
    have hC2R : (2:ℝ) ≤ C := by exact_mod_cast hC2
    have hhC : |(modifiedDerivativeApprox S D.sCap t D.dPhi:ℝ)| ≤ (C:ℝ) := by linarith
    exact_mod_cast hhC
  intro words hwords
  apply D.capped_fold_eq S C (by positivity) ha ha1 hsig0 hsigma hsigma2
    (by rw [hSnapq]; exact hmesh.1) (by rw [hSnapq]; exact hmesh.2)
    (by rw [hRoundq]; exact hmesh.1) (by rw [hRoundq]; exact hmesh.2) hL hcoeff F
    (data_bound S C I m F) words 0
  · simpa only [zero_add] using hwords.trans (stepCount_le_coins S C I m hC2 hm1)
  · intro i; simp

 theorem actual_drift_fuel {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 2 ≤ C) (hm : 1 ≤ m) :
    let F := criticalCoins S C (encodedInput I.1,m)
    let D := sampleEulerData S C I m F
    0 < D.dPhi ∧ 2/(D.dPhi:ℝ)^3+2 ≤ D.fuel.length := by
  let F := criticalCoins S C (encodedInput I.1,m)
  let D := sampleEulerData S C I m F
  let R := SamplerDataFacts.radius S C I m
  have hb := SamplerBudgetBounds.bounds C N m (SamplerDataFacts.trials S C I m) hC hm
  change 2^64 ≤ R ∧ _ at hb
  have hR1 : 1 ≤ R := by omega
  have hp := (SamplerDataFacts.parameters S C I m F).2.1
  change (D.dPhi:ℝ) = 1/(R:ℝ)^100 at hp
  constructor
  · have hh : (0:ℝ) < D.dPhi := by rw [hp]; positivity
    exact_mod_cast hh
  · have hh := drift_exp_fuel R hb.1
    change 2/(D.dPhi:ℝ)^3+2 ≤ (List.replicate F ()).length
    rw [List.length_replicate,show F=R^10000 from coins_eq_radius S C I m,hp]
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast] using hh


end CritWinSpin.LocalTM2.Compiled.SamplerCappedPath
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section













end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open CritWinSpin.Implementation PreprocessPSD SamplerDataFacts
noncomputable section

theorem samplerTrialBits_data {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m F : ℕ) :
    samplerTrialBits S C (encodedSamplerInput I m []) =
      (samplerStepCount S C (sampleReference I m F))*N*
        gaussianNoiseBits (sampleEulerData S C I m F).k +
      acceptanceBits (sampleEulerData S C I m F).k + N*spinBits S (sampleEulerData S C I m F).k := by
  simp only [samplerTrialBits,encodedSamplerInput,List.length_replicate]
  rfl

theorem actual_word_budgets {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 2 ≤ C) (hm : 1 ≤ m) (hqC : (alphabet S).length ≤ C) :
    let F := criticalCoins S C (encodedInput I.1,m)
    let D := sampleEulerData S C I m F
    let Q := trials S C I m
    Q ≤ F  ∧  Q*samplerTrialBits S C (encodedSamplerInput I m []) ≤ F  ∧ 
    (0 < D.dPhi  ∧  2/(D.dPhi:ℝ)^3+2 ≤ D.fuel.length)  ∧ 
    2/(spinPrecision C D.k:ℝ)^3+2 ≤ D.fuel.length  ∧  D.k+1 ≤ D.fuel.length  ∧ 
    2/(1/((D.k:ℝ)+1))^3+2 ≤ (D.fuel.length:ℝ) := by
  let F := criticalCoins S C (encodedInput I.1,m)
  let D := sampleEulerData S C I m F
  let Q := trials S C I m
  let R := radius S C I m
  have hb : 2^64 ≤ R  ∧  N+1 ≤ R  ∧  Q ≤ R  ∧  2*C ≤ R  ∧  C ≤ R := SamplerBudgetBounds.bounds C N m Q hC hm
  have hR1 : 1 ≤ R := by norm_num at hb; omega
  have hFR : F=R^10000 := SamplerCappedPath.coins_eq_radius S C I m
  have hk : D.k=R^100 := by simp only [D,sampleEulerData,samplerQuality,radius_eq,R]
  have hT := (parameters S C I m F).2.2.2.2.2.2.2
  have hFu : D.fuel.length=F := by simp only [D,sampleEulerData,List.length_replicate]
  have hRF : R ≤ F := by rw [hFR]; simpa only [pow_one] using Nat.pow_le_pow_right hR1 (show 1 ≤ (10000:ℕ) by decide)
  have hbits := random_fuel_suffices S R N Q hb.1 (by omega) hb.2.2.1 (hqC.trans hb.2.2.2.2)
  have hspin := spin_exp_fuel C R hb.1 (by omega) hb.2.2.2.2
  have hint := integral_exp_fuel R hb.1
  have htake : D.k+1 ≤ D.fuel.length := by
    rw [hFu,hFR,hk]
    have hh := (gaussianNoiseBits_linear (R^100)).trans (global_gaussian_fuel R hb.1)
    omega
  refine ⟨hb.2.2.1.trans hRF,?_,SamplerCappedPath.actual_drift_fuel S C I m hC hm,?_,htake,?_⟩
  · rw [samplerTrialBits_data S C I m F,hT,hk]
    change Q*(16*2048^2*R^12*N*gaussianNoiseBits (R^100)+
      acceptanceBits (R^100)+N*spinBits S (R^100)) ≤ F
    rw [hFR]
    exact hbits
  · rw [hFu,hFR,hk]
    exact hspin
  · rw [hFu,hFR,hk]
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Rat.cast_add,Rat.cast_pow] using hint

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open IsingLTL.BeliefProp

theorem enumeratedWeights_nonneg {α : Type} (E ρ : α → ℚ) (U d : ℚ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hρ : ∀ x, 0 ≤ ρ x) (hU : ∀ x, E x ≤ U) :
    ∀ x, 0 ≤ enumeratedWeights E ρ U d x := by
  intro x
  exact mul_nonneg (hρ x) (expNegativeApprox_error (U - E x) d
    (sub_nonneg.mpr (hU x)) hd hd1).1

theorem enumeratedWeights_pivot {α : Type} (E ρ : α → ℚ) (U d : ℚ)
    (hd : 0 < d) (xstar : α) (hstar : E xstar = U) :
    enumeratedWeights E ρ U d xstar = ρ xstar := by
  simp [enumeratedWeights, hstar, expNegativeApprox_zero d hd]

theorem enumeratedWeights_sum_positive {α : Type} [Fintype α] (E ρ : α → ℚ) (U d : ℚ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hρ : ∀ x, 0 < ρ x) (hU : ∀ x, E x ≤ U)
    (xstar : α) (hstar : E xstar = U) : 0 < ∑ x, enumeratedWeights E ρ U d x := by
  have hw := enumeratedWeights_nonneg E ρ U d hd hd1 (fun x => (hρ x).le) hU
  have hp := Finset.single_le_sum (fun x _ => hw x) (Finset.mem_univ xstar)
  rw [enumeratedWeights_pivot E ρ U d hd xstar hstar] at hp
  exact (hρ xstar).trans_le hp

theorem normalizedRational_distribution {α : Type} [Fintype α] (w : α → ℚ)
    (hw : ∀ x, 0 ≤ w x) (hW : 0 < ∑ x, w x) :
    IsDistribution (fun x => (w x : ℝ) / ∑ y, (w y : ℝ)) := by
  have hWr : (0 : ℝ) < ∑ x, (w x : ℝ) := by exact_mod_cast hW
  refine ⟨fun x => div_nonneg (by exact_mod_cast hw x) hWr.le, ?_⟩
  rw [← Finset.sum_div]
  exact div_self hWr.ne'

theorem tvDist_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (p q : β → ℝ) : tvDist (fun a => p (e a)) (fun a => q (e a)) = tvDist p q := by
  unfold tvDist
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp CritWinSpin.Implementation.EnvelopeAnalysis
noncomputable section

















end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp
noncomputable section























end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp
noncomputable section

























end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical
noncomputable section

























end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section

def joinNoiseWords {B : ℕ} (words : List (Fin B → Bool)) : List Bool := words.flatMap List.ofFn



theorem eulerFold_of_words {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ) ^ 3 + 2 ≤ D.fuel.length)
    (words : List (Fin (N * gaussianNoiseBits D.k) → Bool)) (z : Fin N → ℚ) (tail : List Bool) :
    (List.replicate words.length ()).foldl (fun st _ => eulerStep S st)
      (D.context, (List.ofFn z, joinNoiseWords words ++ tail)) =
        (D.context, (List.ofFn (words.foldl (D.cappedNext S) z), tail)) := by
  induction words generalizing z with
  | nil => simp [joinNoiseWords]
  | cons w words ih =>
      simp only [List.length_cons, List.replicate_succ, List.foldl_cons,
        joinNoiseWords, List.flatMap_cons, List.append_assoc]
      rw [eulerStep_ofFn S D hd hf]
      exact ih (D.cappedNext S z w)



end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
noncomputable section



theorem EulerData.trialCode_of_words {N : ℕ} (D : EulerData N) (S : SpinLaw) (C T : ℕ)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ)^3 + 2 ≤ D.fuel.length)
    (words : Fin T → Fin (N * gaussianNoiseBits D.k) → Bool) (tail : List Bool) :
    D.trialCode S C T (joinNoiseWords (List.ofFn words) ++ tail) =
      kernelOutput S C (D.kernelInput ((List.ofFn words).foldl (D.cappedNext S) (fun _ => 0)) tail) := by
  unfold EulerData.trialCode
  have he := eulerFold_of_words S D hd hf (List.ofFn words) (fun _ => 0) tail
  simp only [List.length_ofFn] at he
  rw [he]
  rfl




end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.FiniteDraw
open IsingLTL.BeliefProp Classical
noncomputable section



theorem expectation {W A : Type} [Fintype W] [Fintype A] (draw : W → A) (f : A → ℝ) :
    (1 / (Fintype.card W : ℝ)) * ∑ w, f (draw w) = ∑ a, f a * law draw a := by
  have hp (w : W) : f (draw w) = ∑ a, f a * if draw w = a then (1 : ℝ) else 0 := by simp
  simp_rw [hp]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum]
  unfold law
  ring

theorem distribution {W A : Type} [Fintype W] [Nonempty W] [Fintype A] (draw : W → A) :
    IsDistribution (law draw) := by
  have hc : (Fintype.card W : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card W ≠ 0)
  refine ⟨fun a => by unfold law; positivity, ?_⟩
  have he := expectation draw (fun _ => (1 : ℝ))
  simpa [hc] using he.symm

theorem compose {W A B : Type} [Fintype W] [Fintype A] [Fintype B]
    (draw : W → A) (f : A → B) (b : B) :
    law (f ∘ draw) b = ∑ a, if f a = b then law draw a else 0 := by
  have he := expectation draw (fun a => if f a = b then (1 : ℝ) else 0)
  simpa [law, Function.comp_def, ite_mul] using he

theorem product {I W A : Type} [Fintype I] [DecidableEq I] [Fintype W] [Fintype A]
    (draw : I → W → A) (a : I → A) :
    law (fun ω : I → W => fun i => draw i (ω i)) a = ∏ i, law (draw i) (a i) := by
  have hp (ω : I → W) :
      (@ite ℝ ((fun i => draw i (ω i)) = a) (Classical.propDecidable _) 1 0) =
        ∏ i, if draw i (ω i) = a i then (1 : ℝ) else 0 := by
    by_cases h : ∀ i, draw i (ω i) = a i
    · have he : (fun i => draw i (ω i)) = a := funext h
      simp [he, h]
    · have he : (fun i => draw i (ω i)) ≠ a := by intro he; apply h; intro i; exact congrFun he i
      rw [if_neg he]
      symm
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  unfold law
  have hs : (∑ ω : I → W, @ite ℝ ((fun i => draw i (ω i)) = a) (Classical.propDecidable _) 1 0) =
      ∑ ω : I → W, ∏ i, if draw i (ω i) = a i then (1 : ℝ) else 0 :=
    Finset.sum_congr rfl (fun ω _ => hp ω)
  rw [hs, ← Fintype.prod_sum (fun i (w : W) => if draw i w = a i then (1 : ℝ) else 0)]
  simp only [Fintype.card_fun, Nat.cast_pow]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, one_div, inv_pow]

theorem retry {W A : Type} [Fintype W] [Nonempty W] [Fintype A]
    (draw : W → Option A) (Q : ℕ) :
    law (fun ω : Fin Q → W => CritWinSpin.Implementation.FiniteRetry.firstSome
      (fun i => draw (ω i))) = CritWinSpin.Implementation.FiniteRetry.retry (law draw) Q := by
  funext a
  rw [show (fun ω : Fin Q → W => CritWinSpin.Implementation.FiniteRetry.firstSome
      (fun i => draw (ω i))) = CritWinSpin.Implementation.FiniteRetry.firstSome ∘
        (fun ω : Fin Q → W => fun i => draw (ω i)) by rfl, compose]
  have hh : (∑ xs : Fin Q → Option A, @ite ℝ (CritWinSpin.Implementation.FiniteRetry.firstSome xs = a)
      (Classical.propDecidable _) (law (fun ω : Fin Q → W => fun i => draw (ω i)) xs) 0) =
      CritWinSpin.Implementation.FiniteRetry.wordLaw (law draw) Q a := by
    unfold CritWinSpin.Implementation.FiniteRetry.wordLaw CritWinSpin.Implementation.FiniteRetry.wordMass
    apply Finset.sum_congr rfl
    intro xs _
    split_ifs
    · exact product (fun _ : Fin Q => draw) xs
    · rfl
  exact hh.trans (CritWinSpin.Implementation.FiniteRetry.wordLaw_eq_retry (distribution draw) Q a)



theorem source_equiv {U W A : Type} [Fintype U] [Fintype W] [Fintype A]
    (e : U ≃ W) (draw : W → A) : law (draw ∘ e) = law draw := by
  funext a
  unfold law
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end
end CritWinSpin.LocalTM2.FiniteDraw

end

section

set_option autoImplicit false
noncomputable section
open IsingLTL.BeliefProp
open scoped BigOperators

namespace CritWinSpin.Implementation.FiniteKernelTV
variable {A : Type} [Fintype A]









theorem acceptance_tv (p : A → ℝ) (hp : IsDistribution p) (a b : ℝ) :
    tvDist (FiniteRetry.trial p a) (FiniteRetry.trial p b) = |a - b| := by
  have hn : |FiniteRetry.trial p a none - FiniteRetry.trial p b none| = |a - b| := by
    simp only [FiniteRetry.trial]
    have he : (1 - a) - (1 - b) = -(a - b) := by ring
    rw [he, abs_neg]
  have hs (x : A) : |FiniteRetry.trial p a (some x) - FiniteRetry.trial p b (some x)| =
      |a - b| * p x := by
    simp only [FiniteRetry.trial, ← sub_mul, abs_mul, abs_of_nonneg (hp.1 x)]
  unfold tvDist
  rw [Fintype.sum_option, hn]
  simp_rw [hs]
  rw [← Finset.mul_sum, hp.2]
  ring

theorem fixed_acceptance_tv (p q : A → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    tvDist (FiniteRetry.trial p a) (FiniteRetry.trial q a) = a * tvDist p q := by
  unfold tvDist
  rw [Fintype.sum_option]
  simp only [FiniteRetry.trial, sub_self, abs_zero, zero_add]
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg ha]
  rw [← Finset.mul_sum]
  ring

theorem trial_tv (p q : A → ℝ) (hp : IsDistribution p) {a b : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    tvDist (FiniteRetry.trial p a) (FiniteRetry.trial q b) ≤ |a - b| + tvDist p q := by
  have ht := FiniteRetry.tv_triangle (FiniteRetry.trial p a) (FiniteRetry.trial p b) (FiniteRetry.trial q b)
  rw [acceptance_tv p hp a b, fixed_acceptance_tv p q hb] at ht
  have hnonneg : 0 ≤ tvDist p q := by unfold tvDist; positivity
  have hh := mul_le_of_le_one_left hnonneg hb1
  linarith only [ht, hh]



end CritWinSpin.Implementation.FiniteKernelTV
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.KernelAcceptance
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessIntegral



















end CritWinSpin.Implementation.KernelAcceptance
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp
noncomputable section














end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.FiniteDraw
open Classical IsingLTL.BeliefProp
noncomputable section



theorem pair_law {U W A : Type} [Fintype U] [Fintype W] [Fintype A]
    (draw : U → W → A) (a : A) :
    law (fun ω : U × W => draw ω.1 ω.2) a = mean (fun u => law (draw u) a) := by
  unfold law mean
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul, ← Finset.mul_sum]
  ring





end
end CritWinSpin.LocalTM2.FiniteDraw

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled.GenericPacketLaw

def packet (T B A : ℕ) :
    ((Fin T → Fin B → Bool) × (Fin A → Bool)) ≃ (Fin (T*B+A) → Bool) :=
  (Equiv.prodCongr (splitBitEquiv T B).symm (Equiv.refl _)).trans
    (Fin.appendEquiv (T*B) A)

theorem packet_apply {T B A : ℕ} (w : Fin T → Fin B → Bool) (v : Fin A → Bool) :
    packet T B A (w,v) = Fin.append ((splitBitEquiv T B).symm w) v := by
  rfl

theorem split_list {T B : ℕ} (w : Fin T → Fin B → Bool) :
    List.ofFn ((splitBitEquiv T B).symm w) = joinNoiseWords (List.ofFn w) := by
  rw [List.ofFn_mul]
  unfold joinNoiseWords
  rw [ofFn_flatMap]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  have hh := congrFun (congrFun ((splitBitEquiv T B).apply_symm_apply w) i) j
  simpa only [splitBitEquiv_apply,blockIndex] using hh

theorem packet_list {T B A : ℕ} (w : Fin T → Fin B → Bool) (v : Fin A → Bool) :
    List.ofFn (packet T B A (w,v)) = joinNoiseWords (List.ofFn w) ++ List.ofFn v := by
  have h1 := congrArg (fun f : Fin (T*B+A) → Bool => List.ofFn f) (packet_apply w v)
  have h2 := List.ofFn_fin_append ((splitBitEquiv T B).symm w) v
  have h3 := congrArg (fun xs : List Bool => xs ++ List.ofFn v) (split_list w)
  exact h1.trans (h2.trans h3)

end CritWinSpin.LocalTM2.Compiled.GenericPacketLaw

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp MeasureTheory
noncomputable section
attribute [local irreducible] EulerData.trialCode kernelOutput



def trialPacketEquiv {N : ℕ} (S : SpinLaw) (D : EulerData N) (T : ℕ) :
    ((Fin T → Fin (N * gaussianNoiseBits D.k) → Bool) ×
      (Fin (acceptanceBits D.k + N * spinBits S D.k) → Bool)) ≃
    (Fin (T * (N * gaussianNoiseBits D.k) + (acceptanceBits D.k + N * spinBits S D.k)) → Bool) :=
  GenericPacketLaw.packet T (N*gaussianNoiseBits D.k) (acceptanceBits D.k+N*spinBits S D.k)

theorem trialPacketEquiv_list {N : ℕ} (S : SpinLaw) (D : EulerData N) (T : ℕ)
    (w : Fin T → Fin (N * gaussianNoiseBits D.k) → Bool)
    (v : Fin (acceptanceBits D.k + N * spinBits S D.k) → Bool) :
    List.ofFn (trialPacketEquiv S D T (w,v)) = joinNoiseWords (List.ofFn w) ++ List.ofFn v := by
  exact GenericPacketLaw.packet_list w v



theorem trialWordLaw_eq {N : ℕ} (S : SpinLaw) (C : ℕ) (D : EulerData N) (T : ℕ)
    (hd : 0 < D.dPhi) (hf : 2 / (D.dPhi : ℝ)^3 + 2 ≤ D.fuel.length)
    (hcap : ∀ w : Fin T → Fin (N * gaussianNoiseBits D.k) → Bool,
      (List.ofFn w).foldl (D.cappedNext S) (fun _ => 0) = finitePath (D.next S) (fun _ => 0) w)
    (y : Option (Config S (Fin N))) :
    trialWordLaw S C D T y = FiniteDraw.mean (fun w : Fin T → Fin (N * gaussianNoiseBits D.k) → Bool =>
      kernelWordLaw S C D (finitePath (D.next S) (fun _ => 0) w) y) := by
  let draw := fun v : Fin (T * (N * gaussianNoiseBits D.k) +
    (acceptanceBits D.k + N * spinBits S D.k)) → Bool =>
      decConfig S N (D.trialCode S C T (List.ofFn v))
  let f := fun (w : Fin T → Fin (N*gaussianNoiseBits D.k) → Bool)
      (v : Fin (acceptanceBits D.k+N*spinBits S D.k) → Bool) =>
    decConfig S N (kernelOutput S C (D.kernelInput
      (finitePath (D.next S) (fun _ => 0) w) (List.ofFn v)))
  have he := FiniteDraw.source_equiv (trialPacketEquiv S D T) draw
  have hh : draw ∘ trialPacketEquiv S D T = fun wv => f wv.1 wv.2 := by
    funext wv
    dsimp only [draw,f,Function.comp_def]
    apply congrArg (decConfig S N)
    have hw : List.ofFn (trialPacketEquiv S D T wv) =
        joinNoiseWords (List.ofFn wv.1) ++ List.ofFn wv.2 := by
      simpa only [Prod.mk.eta] using trialPacketEquiv_list S D T wv.1 wv.2
    exact (congrArg (D.trialCode S C T) hw).trans
      ((D.trialCode_of_words S C T hd hf wv.1 (List.ofFn wv.2)).trans
        (congrArg (kernelOutput S C)
          (congrArg (fun z => D.kernelInput z (List.ofFn wv.2)) (hcap wv.1))))
  have heY : FiniteDraw.law
      (fun wv : (Fin T → Fin (N*gaussianNoiseBits D.k) → Bool) ×
        (Fin (acceptanceBits D.k+N*spinBits S D.k) → Bool) => f wv.1 wv.2) y = FiniteDraw.law draw y := by
    simpa only [hh] using congrFun he y
  change FiniteDraw.law draw y =
    FiniteDraw.mean (fun w : Fin T → Fin (N*gaussianNoiseBits D.k) → Bool => FiniteDraw.law (f w) y)
  exact heY.symm.trans (FiniteDraw.pair_law f y)







end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp
open CritWinSpin.Implementation
noncomputable section





end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp MeasureTheory
open CritWinSpin.Implementation
noncomputable section

theorem numeric_trajectory_tv {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C : ℕ) (hC : 0<C)
    (D : EulerData N) (T : ℕ) (hs : tau S < (D.sCap:ℝ))
    (hfSpin : 2 / (spinPrecision C D.k:ℝ)^3+2 ≤ D.fuel.length)
    (hTake : D.k+1 ≤ D.fuel.length)
    (hfIntegral : 2 / (1/((D.k:ℝ)+1))^3+2 ≤ (D.fuel.length:ℝ))
    (hnil : decConfig S N [] = none)
    (r : Option (Config S (Fin N)) → ℝ)
    (hmean : ∀ y, r y = FiniteDraw.mean (fun w : Fin T → Fin (N*gaussianNoiseBits D.k) → Bool =>
      kernelWordLaw S C D (finitePath (D.next S) (fun _ => 0) w) y))
    (Ck : ℝ) (hCk : 0 ≤ Ck)
    (hLip : ∀ z w : Fin N → ℝ,
      tvDist (kernelK S (D.sCap:ℝ) (castM D.L) (castV D.h) z)
        (kernelK S (D.sCap:ℝ) (castM D.L) (castV D.h) w) ≤
          Ck * Real.sqrt (N:ℝ) * Real.sqrt (normSq (z-w))) :
    tvDist r
      (fun x => ∫ z, SpinKernel.pointKernel S (D.sCap:ℝ) (castM D.L) (castV D.h) z x
        ∂D.trajectoryLaw S T (fun _ => 0)) ≤
      KernelPrecisionBudget.error S C N D.k (D.sCap:ℝ) := by
  exact CritWinSpin.numeric_kernel_trajectory_tv S hS C hC D T hs hfSpin hTake hfIntegral hnil r hmean Ck hCk hLip

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp MeasureTheory
open CritWinSpin.Implementation PreprocessPSD PreprocessIntegral SamplerDataFacts
noncomputable section

theorem actual_numerical_tv {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C : ℕ) (I : Inst N) (m : ℕ)
    (hC : 131072 ≤ C) (hScale : 1000*(fixedScale S:ℝ) ≤ (C:ℝ))
    (hPrecision : 1000*integrationConstant S ≤ (C:ℝ)) (hqC : (alphabet S).length ≤ C)
    (hN : 0 < N) (hI : I.1.IsSymm) (hm : 5 ≤ m)
    (hin : preInside S C (encodedInput I.1)=true) (Ck : ℝ) (hCk : 0 ≤ Ck)
    (hLip : let F := criticalCoins S C (encodedInput I.1,m)
      let D := sampleEulerData S C I m F
      ∀ z w : Fin N → ℝ,
        tvDist (kernelK S D.sCap (castM D.L) (castV I.2) z)
          (kernelK S D.sCap (castM D.L) (castV I.2) w) ≤
            Ck*Real.sqrt (N:ℝ)*Real.sqrt (normSq (z-w))) :
    let F := criticalCoins S C (encodedInput I.1,m)
    let D := sampleEulerData S C I m F
    let T := samplerStepCount S C (sampleReference I m F)
    tvDist (trialWordLaw S C D T)
      (fun x => ∫ z, SpinKernel.pointKernel S D.sCap (castM D.L) (castV I.2) z x
        ∂D.trajectoryLaw S T (fun _ => 0)) ≤ KernelPrecisionBudget.error S C N D.k D.sCap := by
  let F := criticalCoins S C (encodedInput I.1,m)
  let D := sampleEulerData S C I m F
  let T := samplerStepCount S C (sampleReference I m F)
  let r := trialWordLaw S C D T
  have hC2 : 2 ≤ C := by omega
  have hC8 : 8 ≤ C := by omega
  have hm1 : 1 ≤ m := by omega
  have hDc : D.sCap=preSelectedLevel S C (encodedInput I.1) := rfl
  have hDh : D.h=I.2 := rfl
  have hbounds := PreprocessBranches.selected_bounds S C I.1 hI hC8 hScale hin
  have hs : tau S < (D.sCap:ℝ) := by
    rw [hDc]
    have hb : (0:ℝ) < preBuffer (List.replicate N ()) := by rw [PreprocessSelection.preBuffer_cast]; positivity
    linarith only [hbounds.1,hb]
  have hbudgets := actual_word_budgets S C I m hC2 hm1 hqC
  have hcap : ∀ w : Fin T → Fin (N*gaussianNoiseBits D.k) → Bool,
      (List.ofFn w).foldl (D.cappedNext S) (fun _ => 0) = finitePath (D.next S) (fun _ => 0) w := by
    intro w
    exact SamplerCappedPath.actual_capped_fold_eq S hS C I m hC hScale hPrecision hI hin hm
      (List.ofFn w) (by simp only [List.length_ofFn]; exact le_rfl)
  have hmean := trialWordLaw_eq S C D T hbudgets.2.2.1.1 hbudgets.2.2.1.2 hcap
  have hnum := numeric_trajectory_tv S hS C (by omega) D T hs
    hbudgets.2.2.2.1 hbudgets.2.2.2.2.1 hbudgets.2.2.2.2.2
    (RetryPacketDecoding.decConfig_nil S N hN) r hmean Ck hCk
    (by rw [hDh]; exact hLip)
  rw [hDh] at hnum
  exact hnum

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open Classical
noncomputable section

namespace FiniteDraw







end FiniteDraw

namespace Compiled



section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option Elab.async false
attribute [local irreducible] CritWinSpin.LocalTM2.Compiled.criticalWindowMachine CritWinSpin.LocalTM2.Compiled.kernelOutput CritWinSpin.LocalTM2.Compiled.kernelAcceptance CritWinSpin.LocalTM2.Compiled.trialOnBlock CritWinSpin.LocalTM2.Compiled.samplerRetryOutput CritWinSpin.LocalTM2.Compiled.samplerTrialOutput CritWinSpin.LocalTM2.Compiled.samplerTrialOutputs CritWinSpin.LocalTM2.Compiled.samplerTrialState CritWinSpin.LocalTM2.Compiled.samplerEulerContext CritWinSpin.LocalTM2.Compiled.samplerDriftContext CritWinSpin.LocalTM2.Compiled.samplerRoot CritWinSpin.Implementation.FiniteRetry.retry CritWinSpin.LocalTM2.FiniteDraw.law


end









end Compiled
end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled
open Classical IsingLTL.BeliefProp
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.Implementation PreprocessPSD SamplerDataFacts
noncomputable section
attribute [local irreducible] criticalWindowMachine kernelOutput EulerData.trialCode
  trialOnBlock samplerRetryOutput FiniteRetry.retry FiniteDraw.law

section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option Elab.async false
attribute [local irreducible] CritWinSpin.LocalTM2.Compiled.kernelAcceptance CritWinSpin.LocalTM2.Compiled.samplerTrialOutput CritWinSpin.LocalTM2.Compiled.samplerTrialOutputs CritWinSpin.LocalTM2.Compiled.samplerTrialState CritWinSpin.LocalTM2.Compiled.samplerEulerContext CritWinSpin.LocalTM2.Compiled.samplerDriftContext CritWinSpin.LocalTM2.Compiled.samplerRoot


end








end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness
open Classical IsingLTL.BeliefProp MeasureTheory
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.Implementation PreprocessPSD PreprocessIntegral SamplerDataFacts
noncomputable section

theorem inside_tv {N : ℕ} (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) (C : ℕ)
    (I : Inst N) (m F : ℕ) (D : EulerData N)
    (hF : F = criticalCoins S C (encodedInput I.1,m)) (hD : D = sampleEulerData S C I m F)
    (M0 Ck : ℝ) (hM0 : 0    ≤    M0) (hCk : 0    ≤    Ck)
    (hC : 131072    ≤    C) (hScale : 1000*(fixedScale S:ℝ)    ≤    (C:ℝ))
    (hPrecision : 1000*integrationConstant S    ≤    (C:ℝ))
    (hM0C : 2048*M0    ≤    (C:ℝ)) (hCkC : 2*Ck    ≤    (C:ℝ))
    (hGC : GaussianMoments.sixthConstant    ≤    (C:ℝ))
    (hqC : (alphabet S).length    ≤    C) (hInv : 1/(S.ρ 1:ℝ)    ≤    (C:ℝ))
    (hN : 0 < N) (hI : I.1.IsSymm) (hJPSD : (castM I.1).PosSemidef)
    (hm : 5   ≤   m) (hin : preInside S C (encodedInput I.1) = true)
    (hiW : Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S D.sCap (castM D.L) (castV I.2) z)))
    (hiW2 : Integrable (fun z : Fin N → ℝ => normSq z*Real.exp (-Wpot S D.sCap (castM D.L) (castV I.2) z)))
    (hiU : Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S D.sCap D.a (castM D.L) (castV I.2) z)))
    (hMom : (∫ z : Fin N → ℝ, normSq z*normDens (Wpot S D.sCap (castM D.L) (castV I.2)) z)    ≤    M0*N)
    (hreg : (1/2:ℝ)*(∫ z : Fin N → ℝ,
      |normDens (Ualpha S D.sCap D.a (castM D.L) (castV I.2)) z-
        normDens (Wpot S D.sCap (castM D.L) (castV I.2)) z|)    ≤    (D.a:ℝ)*M0*N/2)
    (hLip : ∀ z w : Fin N → ℝ,
      tvDist (kernelK S D.sCap (castM D.L) (castV I.2) z)
        (kernelK S D.sCap (castM D.L) (castV I.2) w)    ≤   
        Ck*Real.sqrt (N:ℝ)*Real.sqrt (normSq (z-w))) :
    tvDist (outLaw (criticalWindowMachine S C) (tupleCode [encInst I,encBin m]) (decConfig S N))
      (gibbsOpt S (castM I.1) (castV I.2))    ≤    1/(m:ℝ) := by
  subst F
  subst D
  let F := criticalCoins S C (encodedInput I.1,m)
  let D := sampleEulerData S C I m F
  let T := samplerStepCount S C (sampleReference I m F)
  let r := trialWordLaw S C D T
  have hC2 : 2 ≤ C := by omega
  have hm1 : 1 ≤ m := by omega
  have hnum := actual_numerical_tv S hS C I m hC hScale hPrecision hqC hN hI hm hin Ck hCk hLip
  have hwordlaw := sampler_retry_law S C I m hC2 hm1 hqC hN hin
  let draw := fun w : Fin (T*(N*gaussianNoiseBits D.k)+(acceptanceBits D.k+N*spinBits S D.k)) → Bool =>
    decConfig S N (D.trialCode S C T (List.ofFn w))
  have hr : IsDistribution r := FiniteDraw.distribution draw
  exact inside_tv_core S p hS hp C I m F D r hr rfl rfl M0 Ck hM0 hCk hC hScale hPrecision
    hM0C hCkC hGC hqC hInv hN hI hJPSD hm hin hiW hiW2 hiU hMom hreg hLip hnum hwordlaw

end
end CritWinSpin.LocalTM2.Compiled.CriticalSamplerCorrectness

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled.EnumerationProof
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open OAI.MetricKMedian.Binary IsingLTL.BeliefProp
open scoped BigOperators
noncomputable section

abbrev size (S : SpinLaw) (N : ℕ) : ℕ := (alphabet S).length ^ N

theorem size_pos (S : SpinLaw) (N : ℕ) : 0 < size S N := by
  have ha : 0 < (alphabet S).length := by
    have h : (alphabet S) ≠ [] := List.ne_nil_of_mem (show (1 : ℚ) ∈ alphabet S by
      exact Finset.mem_toList.mpr S.one_mem)
    exact List.length_pos_iff.mpr h
  exact pow_pos ha N

abbrev Index (S : SpinLaw) (N : ℕ) := Fin (size S N)
abbrev cfg (S : SpinLaw) (N : ℕ) : Index S N ≃ Config S (Fin N) := configIndexEquiv S N
abbrev vals (S : SpinLaw) (N : ℕ) (k : Index S N) : List ℚ := List.ofFn (fun i => ((cfg S N k) i).1)
abbrev E {S : SpinLaw} {N : ℕ} (I : Inst N) (k : Index S N) : ℚ := energyRational I (cfg S N k)
abbrev base (S : SpinLaw) (N : ℕ) (k : Index S N) : ℚ := configBaseWeight S (cfg S N k)
def records {N : ℕ} (S : SpinLaw) (I : Inst N) : List EnergyRecord :=
  List.ofFn (fun k : Index S N => (vals S N k, E I k, base S N k))
def U {N : ℕ} (S : SpinLaw) (I : Inst N) : ℚ := maximumQ (List.ofFn (E (S := S) I))

theorem energy_list_nonempty {N : ℕ} (S : SpinLaw) (I : Inst N) :
    List.ofFn (E (S := S) I) ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp only [List.length_ofFn, List.length_nil] at hh
  exact (Nat.ne_of_gt (size_pos S N)) hh

theorem energy_le_U {N : ℕ} (S : SpinLaw) (I : Inst N) (k : Index S N) : E I k ≤ U S I := by
  apply le_maximumQ
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

theorem pivot_lt {N : ℕ} (S : SpinLaw) (I : Inst N) :
    (List.ofFn (E (S := S) I)).findIdx (fun z => decide (z = U S I)) < size S N := by
  have hU : U S I ∈ List.ofFn (E (S := S) I) := maximumQ_mem _ (energy_list_nonempty S I)
  have h := List.findIdx_lt_length_of_exists
    (p := fun z : ℚ => decide (z = U S I)) ⟨U S I, hU, by simp⟩
  simpa only [List.length_ofFn] using h

def pivot {N : ℕ} (S : SpinLaw) (I : Inst N) : Index S N :=
  ⟨(List.ofFn (E (S := S) I)).findIdx (fun z => decide (z = U S I)), pivot_lt S I⟩

theorem pivot_energy {N : ℕ} (S : SpinLaw) (I : Inst N) : E I (pivot S I) = U S I := by
  have h := List.findIdx_getElem (xs := List.ofFn (E (S := S) I))
    (p := fun z => decide (z = U S I)) (w := by simpa only [List.length_ofFn] using pivot_lt S I)
  simpa only [List.getElem_ofFn, decide_eq_true_eq, pivot] using h

def tolerance {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) : ℚ :=
  base S N (pivot S I) / (16 * (m : ℚ) * (size S N : ℚ))
def weights {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (k : Index S N) : ℚ :=
  enumeratedWeights (E I) (base S N) (U S I) (tolerance S I m) k
def budget (S : SpinLaw) (N m : ℕ) : ℕ :=
  budgetFromPowers (size S N, ((alphabet S).length * weightDenominatorBound S) ^ N, m)

theorem tolerance_bounds {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m) :
    0 < tolerance S I m ∧ tolerance S I m ≤ 1 := by
  have hn : (0 : ℚ) < size S N := by exact_mod_cast size_pos S N
  have hn1 : (1 : ℚ) ≤ size S N := by exact_mod_cast size_pos S N
  have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hb := configBaseWeight_bounds S (cfg S N (pivot S I))
  have hden : (1 : ℚ) ≤ 16 * m * size S N := by nlinarith
  refine ⟨div_pos hb.2.1 (by positivity), ?_⟩
  exact (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * m * size S N)).mpr (by
    simpa only [one_mul] using hb.2.2.trans hden)

theorem reciprocal_tolerance_le {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m) :
    (1 : ℝ) / (tolerance S I m : ℝ) ≤
      (16 * m * (((alphabet S).length * weightDenominatorBound S) ^ N) : ℕ) := by
  have hb := configBaseWeight_bounds S (cfg S N (pivot S I))
  have hD : (0 : ℝ) < weightDenominatorBound S := by exact_mod_cast weightDenominatorBound_positive S
  have hbR : (1 / (weightDenominatorBound S : ℝ)) ^ N ≤ (base S N (pivot S I) : ℝ) := by
    have hR : ((((1 / (weightDenominatorBound S : ℚ)) ^ N) : ℚ) : ℝ) ≤
        (configBaseWeight S (cfg S N (pivot S I)) : ℝ) := Rat.cast_le.mpr hb.1
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hR
  have hden : (0 : ℝ) < base S N (pivot S I) := by exact_mod_cast hb.2.1
  have hinv : 1 / (base S N (pivot S I) : ℝ) ≤ (weightDenominatorBound S : ℝ) ^ N := by
    rw [div_pow, one_pow] at hbR
    apply (div_le_iff₀ hden).mpr
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < (weightDenominatorBound S : ℝ) ^ N)).mp hbR
    nlinarith
  have htol : (tolerance S I m : ℝ) =
      (base S N (pivot S I) : ℝ) / (16 * m * (size S N : ℝ)) := by
    simp only [tolerance, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
  rw [htol, one_div_div]
  have hmul := mul_le_mul_of_nonneg_left hinv
    (by positivity : (0 : ℝ) ≤ 16 * m * (size S N : ℝ))
  simpa only [div_eq_mul_inv, one_div, size, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    mul_pow, mul_assoc, one_mul] using hmul

theorem exp_fuel_enough {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m)
    (coins : List Bool) (hlen : coins.length = budget S N m) :
    2 / (tolerance S I m : ℝ) ^ 3 + 2 ≤ (coins.map (fun _ => ())).length := by
  have h := reciprocal_tolerance_le S I m hm
  have ht := (tolerance_bounds S I m hm).1
  have htR : (0 : ℝ) < tolerance S I m := by exact_mod_cast ht
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (tolerance S I m : ℝ)) h 3
  simp only [one_div_pow] at hp
  have hlenR : ((coins.map (fun _ => ())).length : ℝ) =
      (tableBits (size S N, m) : ℝ) + size S N +
        2 * ((16 * m * (((alphabet S).length * weightDenominatorBound S) ^ N) : ℕ) : ℝ) ^ 3 + 2 := by
    simp only [List.length_map, hlen, budget, budgetFromPowers, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [hlenR]
  calc
    _ = 2 * (1 / (tolerance S I m : ℝ) ^ 3) + 2 := by ring
    _ ≤ 2 * ((16 * m * (((alphabet S).length * weightDenominatorBound S) ^ N) : ℕ) : ℝ) ^ 3 + 2 := by linarith
    _ ≤ _ := by linarith [show (0 : ℝ) ≤ tableBits (size S N, m) by positivity,
      show (0 : ℝ) ≤ size S N by positivity]

abbrev input {N : ℕ} (I : Inst N) (m : ℕ) (coins : List Bool) : EnumerationInput :=
  ((instanceListModel I, List.replicate N ()), (m, coins))

theorem values_correct_reindexed (S : SpinLaw) (N : ℕ) (sites : List Unit)
    (hs : sites.length = N) (coins : List Bool) (hn : size S N ≤ coins.length) :
    enumerationValues S (sites, coins) = List.ofFn (vals S N) := by
  subst N
  exact enumerationValues_correct S sites coins hn

theorem records_correct {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ)
    (coins : List Bool) (hlen : size S N ≤ coins.length) :
    enumerationRecords S (input I m coins) = records S I := by
  have h : enumerationValues S (List.replicate N (), coins) = List.ofFn (vals S N) := by
    exact values_correct_reindexed S N (List.replicate N ()) (List.length_replicate) coins hlen
  rw [enumerationRecords, input, h, List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  dsimp only [Function.comp_def, Prod.fst, Prod.snd, vals, instanceListModel]
  rw [energyFromLists_correct, baseWeightFromValues_correct]

theorem maximum_correct {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ)
    (coins : List Bool) (hlen : size S N ≤ coins.length) :
    enumerationMaximum S (input I m coins) = U S I := by
  rw [enumerationMaximum, records_correct S I m coins hlen]
  simp only [records, List.map_ofFn, Function.comp_def, U]

theorem pivotWeight_correct {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ)
    (coins : List Bool) (hlen : size S N ≤ coins.length) :
    enumerationPivotWeight S (input I m coins) = base S N (pivot S I) := by
  rw [enumerationPivotWeight, records_correct S I m coins hlen, maximum_correct S I m coins hlen]
  have hfind : (records S I).findIdx (fun r => decide (r.2.1 = U S I)) = (pivot S I).val := by
    have h := List.findIdx_map (records S I) (fun r => r.2.1) (fun z => decide (z = U S I))
    simp only [Function.comp_def] at h
    change _ = (pivot S I).val
    rw [← h]
    simp only [records, List.map_ofFn, Function.comp_def, pivot]
  rw [hfind]
  simp only [records, List.getElem?_ofFn, (pivot S I).isLt, dite_true, Option.getD_some]

theorem tolerance_correct {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ)
    (coins : List Bool) (hlen : size S N ≤ coins.length) :
    enumerationTolerance S (input I m coins) = tolerance S I m := by
  rw [enumerationTolerance, pivotWeight_correct S I m coins hlen,
    records_correct S I m coins hlen]
  simp only [records, List.length_ofFn]
  rfl

theorem weights_correct {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m)
    (coins : List Bool) (hlen : coins.length = budget S N m) :
    enumerationWeights S (input I m coins) = List.ofFn (weights S I m) := by
  have hn : size S N ≤ coins.length := by rw [hlen]; unfold budget budgetFromPowers; omega
  rw [enumerationWeights, records_correct S I m coins hn,
    maximum_correct S I m coins hn, tolerance_correct S I m coins hn]
  simp only [records, List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  change base S N k * expWithFuel ((U S I - E I k, tolerance S I m), coins.map (fun _ => ())) = _
  rw [expWithFuel_eq_uniform _ _ (sub_nonneg.mpr (energy_le_U S I k))
    (tolerance_bounds S I m hm).1 _ (exp_fuel_enough S I m hm coins hlen)]
  rfl

theorem weights_nonneg {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m) :
    ∀ k, 0 ≤ weights S I m k :=
  enumeratedWeights_nonneg _ _ _ _ (tolerance_bounds S I m hm).1
    (tolerance_bounds S I m hm).2 (fun k => (configBaseWeight_bounds S (cfg S N k)).2.1.le)
    (energy_le_U S I)

theorem weights_sum_positive {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m) :
    0 < ∑ k, weights S I m k :=
  enumeratedWeights_sum_positive _ _ _ _ (tolerance_bounds S I m hm).1
    (tolerance_bounds S I m hm).2 (fun k => (configBaseWeight_bounds S (cfg S N k)).2.1)
    (energy_le_U S I) (pivot S I) (pivot_energy S I)

def normWeights {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (k : Index S N) : ℝ :=
  (weights S I m k : ℝ) / ∑ j, (weights S I m j : ℝ)
def firstIndex (S : SpinLaw) (N : ℕ) : Index S N := ⟨0, size_pos S N⟩
def counts {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) : Index S N → ℕ :=
  DyadicRounding.counts (normWeights S I m) (tableCapacity (size S N, m)) (firstIndex S N)

theorem normWeights_distribution {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m) :
    IsDistribution (normWeights S I m) :=
  normalizedRational_distribution _ (weights_nonneg S I m hm) (weights_sum_positive S I m hm)

theorem counts_total {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m) :
    ∑ k, counts S I m k = 2 ^ tableBits (size S N, m) :=
  DyadicRounding.counts_total _ (normWeights_distribution S I m hm) _ _

theorem quantizedCounts_ofFn_positive {n : ℕ} (hn : 0 < n) (w : Fin n → ℚ) (T : ℕ) :
    quantizedCounts (List.ofFn w, T) = List.ofFn (DyadicRounding.counts
      (fun i => (w i : ℝ) / ∑ j, (w j : ℝ)) T ⟨0, hn⟩) := by
  cases n with
  | zero => omega
  | succ n => exact quantizedCounts_ofFn w T

theorem counts_correct {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m)
    (coins : List Bool) (hlen : coins.length = budget S N m) :
    enumerationCounts S (input I m coins) = List.ofFn (counts S I m) := by
  have hn : size S N ≤ coins.length := by rw [hlen]; unfold budget budgetFromPowers; omega
  rw [enumerationCounts, weights_correct S I m hm coins hlen, records_correct S I m coins hn]
  simp only [records, List.length_ofFn]
  exact quantizedCounts_ofFn_positive (size_pos S N) _ _

theorem take_ofFn_prefix (L R : ℕ) (ω : Fin (L + R) → Bool) :
    (List.ofFn ω).take L = List.ofFn (fun i => ω (Fin.castAdd R i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_take, List.getElem_ofFn]
    rfl

theorem budget_split (S : SpinLaw) (N m : ℕ) :
    budget S N m = tableBits (size S N, m) + (budget S N m - tableBits (size S N, m)) := by
  unfold budget budgetFromPowers
  dsimp only
  omega

theorem selected_correct {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m)
    (ω : Fin (tableBits (size S N, m) + (budget S N m - tableBits (size S N, m))) → Bool) :
    enumerationSelected S (input I m (List.ofFn ω)) =
      vals S N (FiniteTicket.drawIndex (tableBits (size S N, m)) (counts S I m)
        (counts_total S I m hm) (fun i => ω (Fin.castAdd _ i))) := by
  have hlen : (List.ofFn ω).length = budget S N m := by
    rw [List.length_ofFn, ← budget_split]
  have hn : size S N ≤ (List.ofFn ω).length := by rw [hlen]; unfold budget budgetFromPowers; omega
  unfold enumerationSelected
  rw [records_correct S I m _ hn, counts_correct S I m hm _ hlen]
  simp only [records, List.map_ofFn, List.length_ofFn, Function.comp_def]
  change sampleFiniteTable ((List.ofFn (vals S N), List.ofFn (counts S I m)),
    (List.ofFn ω).take (tableBits (size S N, m))) = _
  rw [take_ofFn_prefix]
  exact sampleFiniteTable_ofFn _ _ _ (counts_total S I m hm) _

theorem actual_law {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m) :
    outLaw (exhaustiveRandMachine S) (tupleCode [encInst I, encBin m]) (decConfig S N) =
      (fun y => Option.elim y 0 (fun x =>
        (counts S I m ((cfg S N).symm x) : ℝ) / (2 : ℝ) ^ tableBits (size S N, m))) := by
  apply table_machine_law (cfg S N) _ _ _ (tableBits (size S N, m))
    (budget S N m - tableBits (size S N, m)) (counts S I m) (counts_total S I m hm)
  · exact (exhaustiveRandMachine_coins S I m).trans (budget_split S N m)
  · intro ω
    rw [exhaustiveRandMachine_run, selected_correct S I m hm ω]
    change decConfig S N ((List.ofFn (fun i =>
      ((cfg S N (FiniteTicket.drawIndex _ _ _ _)) i).1)).flatMap encRat) = _
    rw [ofFn_flatMap]
    exact decConfig_encConfig _

theorem indexed_gibbs {N : ℕ} (S : SpinLaw) (I : Inst N) (k : Index S N) :
    (Real.exp (E I k : ℝ) * (base S N k : ℝ)) /
        ∑ j, Real.exp (E I j : ℝ) * (base S N j : ℝ) =
      gibbs S (castM I.1) (castV I.2) (cfg S N k) := by
  rw [gibbs_rational_energy]
  congr 1
  exact (cfg S N).sum_comp (fun x => Real.exp (energyRational I x : ℝ) * (configBaseWeight S x : ℝ))

theorem weights_tv {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 0 < m) :
    tvDist (normWeights S I m) (fun k => gibbs S (castM I.1) (castV I.2) (cfg S N k)) ≤
      1 / (16 * (m : ℝ)) := by
  have h := enumeratedWeights_tv (E (S := S) I) (base S N) (U S I) (tolerance S I m)
    (tolerance_bounds S I m hm).1 (tolerance_bounds S I m hm).2
    (fun k => ⟨(configBaseWeight_bounds S (cfg S N k)).2.1,
      (configBaseWeight_bounds S (cfg S N k)).2.2⟩)
    (energy_le_U S I) (pivot S I) (pivot_energy S I)
  simp only [indexed_gibbs] at h
  have hn : (size S N : ℝ) ≠ 0 := by exact_mod_cast (size_pos S N).ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hb : (base S N (pivot S I) : ℝ) ≠ 0 := by
    exact_mod_cast (configBaseWeight_bounds S (cfg S N (pivot S I))).2.1.ne'
  have hbound : (Fintype.card (Index S N) : ℝ) * tolerance S I m /
      (base S N (pivot S I) : ℝ) = 1 / (16 * (m : ℝ)) := by
    simp only [Index, Fintype.card_fin, tolerance, Rat.cast_div, Rat.cast_mul,
      Rat.cast_natCast, Rat.cast_ofNat]
    field_simp
  exact h.trans_eq hbound

theorem option_tv {α : Type} [Fintype α] (p q : α → ℝ) :
    tvDist (fun y => Option.elim y 0 p) (fun y => Option.elim y 0 q) = tvDist p q := by
  simp only [tvDist, Fintype.sum_option, Option.elim_none, Option.elim_some,
    sub_self, abs_zero, zero_add]

theorem exhaustiveRandMachine_tv {N : ℕ} (S : SpinLaw) (I : Inst N) (m : ℕ) (hm : 5 ≤ m) :
    tvDist (outLaw (exhaustiveRandMachine S) (tupleCode [encInst I, encBin m]) (decConfig S N))
      (gibbsOpt S (castM I.1) (castV I.2)) ≤ 1 / (m : ℝ) := by
  have hmpos : 0 < m := by omega
  rw [actual_law S I m hmpos]
  have hg : gibbsOpt S (castM I.1) (castV I.2) =
      (fun y => Option.elim y 0 (gibbs S (castM I.1) (castV I.2))) := by
    funext y
    cases y <;> rfl
  rw [hg]
  change tvDist (fun y => Option.elim y 0 (fun x =>
      (counts S I m ((cfg S N).symm x) : ℝ) / (2 : ℝ) ^ tableBits (size S N, m)))
    (fun y => Option.elim y 0 (gibbs S (castM I.1) (castV I.2))) ≤ _
  rw [option_tv, ← tvDist_equiv (cfg S N)]
  simp only [Equiv.symm_apply_apply]
  have hround := DyadicRounding.tv_error _ (normWeights_distribution S I m hmpos)
    (tableCapacity (size S N, m)) (by unfold tableCapacity; positivity) (firstIndex S N)
  have hround' : tvDist
      (fun k => (counts S I m k : ℝ) / (2 : ℝ) ^ tableBits (size S N, m))
      (normWeights S I m) ≤ 1 / (4 * (m : ℝ)) := by
    have h : tvDist
        (fun k => (counts S I m k : ℝ) / (2 : ℝ) ^ tableBits (size S N, m))
        (normWeights S I m) ≤ (size S N : ℝ) / (2 : ℝ) ^ tableBits (size S N, m) := by
      simpa only [Fintype.card_fin, counts, tableCapacity, Nat.cast_pow, Nat.cast_ofNat] using hround
    exact h.trans (tableRounding_error_bound (size S N) m hmpos)
  have htri := tv_triangle
    (fun k => (counts S I m k : ℝ) / (2 : ℝ) ^ tableBits (size S N, m))
    (normWeights S I m) (fun k => gibbs S (castM I.1) (castV I.2) (cfg S N k))
  have happrox := weights_tv S I m hmpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hsum : 1 / (4 * (m : ℝ)) + 1 / (16 * (m : ℝ)) ≤ 1 / (m : ℝ) := by
    have heq : 1 / (4 * (m : ℝ)) + 1 / (16 * (m : ℝ)) = (5 / 16 : ℝ) * (1 / m) := by
      field_simp
      <;> ring
    rw [heq]
    nlinarith [show (0 : ℝ) ≤ 1 / (m : ℝ) by positivity]
  exact htri.trans ((add_le_add hround' happrox).trans hsum)

end
end CritWinSpin.LocalTM2.Compiled.EnumerationProof

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled.SamplerBranchCorrectness
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC IsingLTL.BeliefProp

theorem outLaw_same_run {α : Type} (M E : RandMachine) (x : Str) (dec : Str → Option α)
    (hc : M.coins x = E.coins x) (hr : ∀ ω : Str,
      M.run (tupleCode [ω,x]) = E.run (tupleCode [ω,x])) : outLaw M x dec = outLaw E x dec := by
  classical
  funext y
  rw [outLaw_reclock M x dec y (E.coins x) hc, outLaw_reclock E x dec y (E.coins x) rfl]
  simp only [hr]

theorem outside_law {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hN : 0 < N)
    (hout : preInside S C (CritWinSpin.Implementation.PreprocessPSD.encodedInput I.1) = false) :
    outLaw (criticalWindowMachine S C) (tupleCode [encInst I, encBin m]) (decConfig S N) =
      outLaw (exhaustiveRandMachine S) (tupleCode [encInst I, encBin m]) (decConfig S N) := by
  have hempty : (List.replicate N ()).isEmpty = false := by cases N <;> simp_all
  change preInside S C ((instanceListModel I).1, List.replicate N ()) = false at hout
  apply outLaw_same_run
  · rw [criticalWindowMachine_coins_encoded, hempty, hout]
    change enumerationBudget S ((instanceListModel I, List.replicate N ()), m) = _
    rw [exhaustiveRandMachine_coins]
    simp only [enumerationBudget, List.map_replicate, naturalProduct_eq, List.prod_replicate]
  · intro ω
    rw [criticalWindowMachine_run_encoded, exhaustiveRandMachine_run, hempty, hout]
    rfl

theorem outside_tv {N : ℕ} (S : SpinLaw) (C : ℕ) (I : Inst N) (m : ℕ)
    (hN : 0 < N)
    (hout : preInside S C (CritWinSpin.Implementation.PreprocessPSD.encodedInput I.1) = false)
    (hm : 5 ≤ m) :
    tvDist (outLaw (criticalWindowMachine S C) (tupleCode [encInst I, encBin m]) (decConfig S N))
      (gibbsOpt S (castM I.1) (castV I.2)) ≤ 1 / (m : ℝ) := by
  rw [outside_law S C I m hN hout]
  exact EnumerationProof.exhaustiveRandMachine_tv S I m hm

theorem zero_dim_law (S : SpinLaw) (C : ℕ) (I : Inst 0) (m : ℕ) :
    outLaw (criticalWindowMachine S C) (tupleCode [encInst I, encBin m]) (decConfig S 0) =
      gibbsOpt S (castM I.1) (castV I.2) := by
  classical
  let empty : Config S (Fin 0) := fun i => Fin.elim0 i
  have hdec : decConfig S 0 [] = some empty := by
    simpa [encConfig] using decConfig_encConfig empty
  have hc : (criticalWindowMachine S C).coins (tupleCode [encInst I,encBin m]) = 0 := by
    rw [criticalWindowMachine_coins_encoded]
    rfl
  have hr (ω : Str) : (criticalWindowMachine S C).run
      (tupleCode [ω,tupleCode [encInst I,encBin m]]) = [] := by
    rw [criticalWindowMachine_run_encoded]
    rfl
  funext y
  rw [outLaw_reclock _ _ _ y 0 hc]
  simp only [hr]
  cases y with
  | none => simp [hdec,gibbsOpt]
  | some y =>
    have hy : y = empty := Subsingleton.elim _ _
    subst y
    simp [hdec,gibbsOpt,gibbs,gibbsWeight,energy,prodRho]

theorem zero_dim_tv (S : SpinLaw) (C : ℕ) (I : Inst 0) (m : ℕ) :
    tvDist (outLaw (criticalWindowMachine S C) (tupleCode [encInst I, encBin m]) (decConfig S 0))
      (gibbsOpt S (castM I.1) (castV I.2)) = 0 := by
  rw [zero_dim_law]
  simp [tvDist]

end CritWinSpin.LocalTM2.Compiled.SamplerBranchCorrectness

end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.RuntimeArithmetic







end CritWinSpin.Implementation.RuntimeArithmetic
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessCriticalLevel
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches



end CritWinSpin.Implementation.PreprocessCriticalLevel
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.CriticalCapBudget
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessCriticalLevel PreprocessIntegral PreprocessCap











end CritWinSpin.Implementation.CriticalCapBudget
end

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2





end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary







end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerRuntime
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled
open PreprocessPSD PreprocessBranches PreprocessIntegral PreprocessCap RuntimeArithmetic











end CritWinSpin.Implementation.SamplerRuntime
end

end

section

set_option autoImplicit false
noncomputable section

namespace CritWinSpin.Implementation.SamplerConstantChoice
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled

theorem choose_constant (S : SpinLaw) (M0 Ck : ℝ) :
    ∃ C : ℕ, 131072 ≤ C ∧
      1000*(fixedScale S : ℝ) ≤ (C : ℝ) ∧
      1000*PreprocessIntegral.integrationConstant S ≤ (C : ℝ) ∧
      2048*M0 ≤ (C : ℝ) ∧ 2*Ck ≤ (C : ℝ) ∧
      GaussianMoments.sixthConstant ≤ (C : ℝ) ∧
      ((alphabet S).length : ℝ) ≤ (C : ℝ) ∧
      (S.ρ 1 : ℝ)⁻¹ ≤ (C : ℝ) := by
  let B : ℝ := 131072 + 1000*|(fixedScale S : ℝ)| +
    1000*|PreprocessIntegral.integrationConstant S| + 2048*|M0| + 2*|Ck| +
    |GaussianMoments.sixthConstant| + |((alphabet S).length : ℝ)| + |(S.ρ 1 : ℝ)⁻¹|
  obtain ⟨C,hC⟩ := exists_nat_ge B
  have h1 := abs_nonneg (fixedScale S : ℝ)
  have h2 := abs_nonneg (PreprocessIntegral.integrationConstant S)
  have h3 := abs_nonneg M0
  have h4 := abs_nonneg Ck
  have h5 := abs_nonneg GaussianMoments.sixthConstant
  have h6 := abs_nonneg ((alphabet S).length : ℝ)
  have h7 := abs_nonneg ((S.ρ 1 : ℝ)⁻¹)
  dsimp only [B] at hC
  refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh : (131072 : ℝ) ≤ C := by
      nlinarith only [hC,h1,h2,h3,h4,h5,h6,h7]
    exact_mod_cast hh
  · nlinarith only [hC,h1,h2,h3,h4,h5,h6,h7,le_abs_self (fixedScale S : ℝ)]
  · nlinarith only [hC,h1,h2,h3,h4,h5,h6,h7,
      le_abs_self (PreprocessIntegral.integrationConstant S)]
  · nlinarith only [hC,h1,h2,h3,h4,h5,h6,h7,le_abs_self M0]
  · nlinarith only [hC,h1,h2,h3,h4,h5,h6,h7,le_abs_self Ck]
  · nlinarith only [hC,h1,h2,h3,h4,h5,h6,h7,
      le_abs_self GaussianMoments.sixthConstant]
  · nlinarith only [hC,h1,h2,h3,h4,h5,h6,h7,
      le_abs_self ((alphabet S).length : ℝ)]
  · nlinarith only [hC,h1,h2,h3,h4,h5,h6,h7,le_abs_self ((S.ρ 1 : ℝ)⁻¹)]

end CritWinSpin.Implementation.SamplerConstantChoice
end

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory IsingLTL.BeliefProp CritWinSpin
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin.LocalTM2.Compiled CritWinSpin.Implementation
open PreprocessPSD PreprocessSelection PreprocessBranches PreprocessIntegral

theorem solution (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) (hP : ∀ (S : SpinLaw) (hS : IsGHS S), ∃ M₀ Cₖ : ℝ, 0 < M₀ ∧ 0 < Cₖ ∧
      ∀ (N : ℕ) (L : Matrix (Fin N) (Fin N) ℝ) (s α : ℝ) (h : Fin N → ℝ),
        tau S < s → s  ≤  2 * tau S + 1 →
        (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef →
        0 < α → α  ≤  1 →
        (∀ᵐ z : Fin N → ℝ,
          DifferentiableAt ℝ (fderiv ℝ (Wpot S s L h)) z ∧
          DifferentiableAt ℝ (fderiv ℝ (Ualpha S s α L h)) z ∧
          ∀ v : Fin N → ℝ,
            0  ≤  fderiv ℝ (fderiv ℝ (Wpot S s L h)) z v v ∧
            fderiv ℝ (fderiv ℝ (Wpot S s L h)) z v v  ≤  normSq v ∧
            α * normSq v  ≤  fderiv ℝ (fderiv ℝ (Ualpha S s α L h)) z v v ∧
            fderiv ℝ (fderiv ℝ (Ualpha S s α L h)) z v v  ≤  (1 + α) * normSq v) ∧
        (Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z)) ∧
          Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Wpot S s L h z)) ∧
          Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S s α L h z)) ∧
          Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Ualpha S s α L h z)) ∧
          max (∫ z : Fin N → ℝ, normSq z * normDens (Wpot S s L h) z)
              (∫ z : Fin N → ℝ, normSq z * normDens (Ualpha S s α L h) z)  ≤  M₀ * (N : ℝ) ∧
          (1 / 2) * (∫ z : Fin N → ℝ,
              |normDens (Ualpha S s α L h) z - normDens (Wpot S s L h) z|)  ≤ 
            α * M₀ * (N : ℝ) / 2) ∧
        (∀ z w : Fin N → ℝ,
          tvDist (kernelK S s L h z) (kernelK S s L h w)  ≤ 
            Cₖ * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w)))) :
    ∃ (M : RandMachine) (C : ℝ) (k : ℕ),
      ∀ (N : ℕ) (I : Inst N) (m : ℕ) (δ : ℝ),
        I.1.IsSymm → (castM I.1).PosSemidef → 0  ≤  δ →
        ((tau S * (1 + δ)) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM I.1).PosSemidef → 5  ≤  m →
        tvDist (outLaw M (tupleCode [encInst I, encBin m]) (decConfig S N))
            (gibbsOpt S (castM I.1) (castV I.2))  ≤  1 / (m : ℝ) ∧
        (M.time (tupleCode [encInst I, encBin m]) : ℝ)  ≤ 
          C * ((N : ℝ) + (bitLen I : ℝ) + (m : ℝ)) ^ k *
            Real.exp (C * (N : ℝ) * δ ^ ((p : ℝ) / ((p : ℝ) - 1))) := by
  obtain ⟨M0,Ck,hM0,hCk,hP0⟩ := hP S hS
  obtain ⟨C,hC,hScale,hPrecision,hM0C,hCkC,hGC,hqC,hInv⟩ :=
    SamplerConstantChoice.choose_constant S M0 Ck
  have hC8 : 8  ≤  C := by omega
  obtain ⟨Ctime,k,hCtime,hTime⟩ :=
    SamplerRuntime.criticalWindowMachine_time S p hS hp C hC8 hScale hPrecision
  refine ⟨criticalWindowMachine S C,Ctime,k,?_⟩
  intro N I m δ hI hJPSD hδ hUpper hm
  refine ⟨?_,hTime N I m δ hI hJPSD hδ hUpper hm⟩
  by_cases hN0 : N=0
  · subst N
    rw [SamplerBranchCorrectness.zero_dim_tv]
    positivity
  have hN : 0<N := Nat.pos_of_ne_zero hN0
  by_cases hin : preInside S C (encodedInput I.1) = true
  · let F := criticalCoins S C (encodedInput I.1,m)
    let D := sampleEulerData S C I m F
    have hCert := SamplerMatrixCertificate.sampler_matrix_certificate S C I m
      hI hJPSD hC8 hScale hin hm
    have hPSD : ((D.sCap:ℝ) • (1:Matrix (Fin N) (Fin N) ℝ)-
        castM D.L*(castM D.L).transpose).PosSemidef := by
      simpa only [D,F,sampleEulerData,SamplerMatrixCertificate.covariance] using hCert.2.2.2.2.1
    have hParams := SamplerDataFacts.parameters S C I m F
    have hCap : D.sCap = preSelectedLevel S C (encodedInput I.1) := hParams.2.2.2.2.2.2.1
    have hBounds := selected_bounds S C I.1 hI hC8 hScale hin
    have hs : tau S < (D.sCap:ℝ) := by
      rw [hCap]
      have hbuf : (0:ℝ) < preBuffer (List.replicate N ()) := by
        rw [preBuffer_cast]
        positivity
      linarith only [hBounds.1,hbuf]
    have hsUpper : (D.sCap:ℝ)  ≤  2*tau S+1 := by
      rw [hCap]
      exact hBounds.2.1
    have hBpos : 0 < SamplerDataFacts.budgetBase S C I m := by
      unfold SamplerDataFacts.budgetBase
      exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have hA : (D.a:ℝ) = 1/(SamplerDataFacts.budgetBase S C I m:ℝ) := hParams.1
    have ha : 0 < (D.a:ℝ) := by rw [hA]; positivity
    have ha1 : (D.a:ℝ)  ≤  1 := by
      rw [hA]
      have hb : (1:ℝ)  ≤  SamplerDataFacts.budgetBase S C I m := by
        exact_mod_cast (show 1  ≤  SamplerDataFacts.budgetBase S C I m by omega)
      simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hb
    obtain ⟨_,hIntegrable,hLip⟩ :=
      hP0 N (castM D.L) D.sCap D.a (castV I.2) hs hsUpper hPSD ha ha1
    have hMom : (∫ z : Fin N → ℝ, normSq z*normDens
        (Wpot S D.sCap (castM D.L) (castV I.2)) z)  ≤  M0*N :=
      (le_max_left _ _).trans hIntegrable.2.2.2.2.1
    exact CriticalSamplerCorrectness.inside_tv S p hS hp C I m F D rfl rfl M0 Ck hM0.le hCk.le
      hC hScale hPrecision hM0C hCkC hGC (by exact_mod_cast hqC)
      (by simpa only [one_div] using hInv) hN hI hJPSD hm hin
      hIntegrable.1 hIntegrable.2.1 hIntegrable.2.2.1 hMom hIntegrable.2.2.2.2.2 hLip
  · exact SamplerBranchCorrectness.outside_tv S C I m hN (Bool.eq_false_iff.mpr hin) hm

end

end
