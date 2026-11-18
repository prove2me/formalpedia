-- Prove2me | solution 1 for CritWinSpin.numeric_kernel_trajectory_tv
-- status  : ACCEPTED   (prove)
-- author  : @Maxliu
-- created : 2026-11-17T18:29:09.212191+00:00
-- url     : https://prove2.me/submissions/fc2f4a02-0390-400c-8ec9-5e494a8a2593

import Definitions.Def_CritWinSpin_SamplerNumericalData

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



theorem gs_even (S : SpinLaw) (s t : ℝ) : gs S s (-t) = gs S s t := by
  simp only [gs_eq_fs_max, abs_neg]

theorem ds_even (S : SpinLaw) (s t : ℝ) : ds S s (-t) = ds S s t := by
  unfold ds; rw [fs_even, gs_even]



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



inductive BinaryPhase | tag | value | skip | copy deriving DecidableEq
instance : Fintype BinaryPhase := ⟨{.tag, .value, .skip, .copy}, by intro p; cases p <;> simp⟩

























































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

theorem law_distribution {α : Type} [Fintype α] (p : α → ℝ) (hp : IsDistribution p)
    (T : ℕ) (hT : 0 < T) (a₀ : α) :
    IsDistribution (fun a => (counts p T a₀ a : ℝ) / T) := by
  classical
  refine ⟨fun _ => by positivity, ?_⟩
  rw [← Finset.sum_div, ← Nat.cast_sum, counts_total p hp T a₀]
  exact div_self (by exact_mod_cast hT.ne')

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













end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

















noncomputable def alphabetEquiv (S : SpinLaw) :
    Fin (alphabet S).length ≃ {a : ℚ // a ∈ S.A} :=
  (List.Nodup.getEquiv (alphabet S) S.A.nodup_toList).trans
    (Equiv.subtypeEquivRight (fun a : ℚ => show a ∈ alphabet S ↔ a ∈ S.A from Finset.mem_toList))



theorem alphabetEquiv_value (S : SpinLaw) (i : Fin (alphabet S).length) :
    ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ) = (alphabet S)[i.val] := rfl



































end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC





end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic










































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







end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
noncomputable section







theorem realRound_cast (x d : ℚ) : realRound (d : ℝ) (x : ℝ) = (roundTowardZero (x, d) : ℝ) := by
  by_cases hx : x < 0
  · have hxR : (x : ℝ) < 0 := by exact_mod_cast hx
    simp only [realRound, roundTowardZero, hxR, hx, ite_true, Rat.cast_mul,
      Rat.cast_neg, Rat.cast_natCast, rationalFloor_real]
    simp
  · have hxR : ¬(x : ℝ) < 0 := by exact_mod_cast hx
    simp only [realRound, roundTowardZero, hxR, hx, ite_false, Rat.cast_mul,
      Rat.cast_natCast, rationalFloor_real]
    simp







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























end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

















end CritWinSpin.LocalTM2

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
open Matrix











end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix









end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open Matrix























end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
































































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
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open CritWinSpin.Implementation.EnvelopeGeometry
noncomputable section



theorem rationalRound_cast (d : ℚ) (x : ℝ) :
    (rationalRound d x : ℝ) = realRound (d : ℝ) x := by
  by_cases hx : x < 0 <;> simp [rationalRound, realRound, hx]

theorem rationalRound_rat (d x : ℚ) : rationalRound d (x : ℝ) = roundTowardZero (x, d) := by
  apply Rat.cast_injective (α := ℝ)
  rw [rationalRound_cast, realRound_cast]























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






























































end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic IsingLTL.BeliefProp

theorem quantizedCounts_ofFn_pos {n : ℕ} (hn : 0 < n) (w : Fin n → ℚ) (T : ℕ) :
    quantizedCounts (List.ofFn w, T) =
      List.ofFn (DyadicRounding.counts
        (fun i => (w i : ℝ) / ∑ j, (w j : ℝ)) T ⟨0, hn⟩) := by
  cases n with
  | zero => omega
  | succ n => exact quantizedCounts_ofFn w T





theorem sampleScalarTable_ofFn {n : ℕ} (v : Fin n → ℚ)
    (L : ℕ) (cs : Fin n → ℕ) (htotal : ∑ i, cs i = 2 ^ L) (ω : Fin L → Bool) :
    sampleScalarTable ((List.ofFn v, List.ofFn cs), List.ofFn ω) =
      v (FiniteTicket.drawIndex L cs htotal ω) := by
  unfold sampleScalarTable
  rw [bucketScan_eq, wordValue_wordNumber, ← FiniteTicket.bitTicket_wordNumber]
  have hb := (FiniteTicket.drawIndex L cs htotal ω).isLt
  change FiniteTicket.bucket (List.ofFn cs) (FiniteTicket.bitTicketEquiv L ω).val < n at hb
  simp only [List.getElem?_ofFn, hb, dite_true, Option.getD_some]
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














end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic











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



end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open CritWinSpin.Implementation.EnvelopeAnalysis





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
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
noncomputable section





theorem finitePath_cons {X W : Type} (step : X → W → X) (x : X) (T : ℕ)
    (ω : Fin (T + 1) → W) :
    finitePath step x ω = finitePath step (step x (ω 0)) (fun i => ω i.succ) := by
  rw [finitePath, List.ofFn_succ, List.foldl_cons]
  rfl

theorem finitePath_expectation {X W : Type} [Fintype W] [Nonempty W]
    (step : X → W → X) (f : X → ℝ) (T : ℕ) (x : X) :
    (1 / (Fintype.card W : ℝ) ^ T) *
        (∑ ω : Fin T → W, f (finitePath step x ω)) =
      ((finiteOperator step)^[T] f) x := by
  classical
  have hc : (Fintype.card W : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card W ≠ 0)
  induction T generalizing x with
  | zero => simp [finitePath]
  | succ T ih =>
      have hs : (∑ ω : Fin (T + 1) → W, f (finitePath step x ω)) =
          ∑ w : W, ∑ ω : Fin T → W, f (finitePath step (step x w) ω) := by
        calc
          _ = ∑ p : W × (Fin T → W), f (finitePath step (step x p.1) p.2) := by
            apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (T + 1) => W)).symm
            intro ω
            simp [finitePath_cons, Fin.tail]
            rfl
          _ = _ := Fintype.sum_prod_type _
      rw [hs, pow_succ, Function.iterate_succ_apply', finiteOperator]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [← ih (step x w)]
      simp only [one_div, mul_inv_rev]
      ring_nf
      rw [Finset.mul_sum]

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







theorem EulerData.realStep_cast {N : ℕ} (D : EulerData N) (S : SpinLaw)
    (z : Fin N → ℚ) (ω : Fin (N * gaussianNoiseBits D.k) → Bool) :
    D.realStep S (WithLp.toLp 2 (castV z)) ω = WithLp.toLp 2 (castV (D.next S z ω)) := by
  have hproject : rationalProject D.snap (WithLp.toLp 2 (castV z)) =
      (fun i => roundTowardZero (z i, D.snap)) := by
    funext i
    exact rationalRound_rat D.snap (z i)
  ext i
  change realRound (D.dRound : ℝ)
    ((z i : ℝ) - (D.sigma : ℝ) ^ 2 *
      (approximateGradient S D.L D.h (rationalProject D.snap (WithLp.toLp 2 (castV z)))
        D.sCap D.a D.dPhi i : ℝ) + (D.sigma : ℝ) *
          (gaussianDraw (D.k, List.ofFn (fun j => ω (blockIndex i j))) : ℝ)) = _
  rw [hproject]
  have hraw : ((z i : ℝ) - (D.sigma : ℝ) ^ 2 *
      (approximateGradient S D.L D.h (fun i => roundTowardZero (z i, D.snap))
        D.sCap D.a D.dPhi i : ℝ) + (D.sigma : ℝ) *
          (gaussianDraw (D.k, List.ofFn (fun j => ω (blockIndex i j))) : ℝ)) =
      (D.raw S z ω i : ℝ) := by
    simp only [EulerData.raw, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow]
  rw [hraw]
  exact realRound_cast _ _



theorem EulerData.realPath_cast {N : ℕ} (D : EulerData N) (S : SpinLaw)
    (T : ℕ) (z : Fin N → ℚ)
    (ω : Fin T → (Fin (N * gaussianNoiseBits D.k) → Bool)) :
    finitePath (D.realStep S) (WithLp.toLp 2 (castV z)) ω =
      WithLp.toLp 2 (castV (finitePath (D.next S) z ω)) := by
  induction T generalizing z with
  | zero => rfl
  | succ T ih =>
      rw [finitePath_cons, finitePath_cons, D.realStep_cast]
      exact ih (D.next S z (ω 0)) (fun i => ω i.succ)

theorem EulerData.word_expectation {N : ℕ} (D : EulerData N) (S : SpinLaw)
    (T : ℕ) (z : Fin N → ℚ) (f : Point N → ℝ) :
    (1 / (Fintype.card (Fin (N * gaussianNoiseBits D.k) → Bool) : ℝ) ^ T) *
      (∑ ω : Fin T → (Fin (N * gaussianNoiseBits D.k) → Bool),
        f (WithLp.toLp 2 (castV (finitePath (D.next S) z ω)))) =
      ((D.operator S)^[T] f) (WithLp.toLp 2 (castV z)) := by
  have hop : D.operator S = finiteOperator (D.realStep S) := rfl
  rw [hop]
  have he := finitePath_expectation (D.realStep S) f T (WithLp.toLp 2 (castV z))
  simpa only [D.realPath_cast] using he





theorem EulerData.integral_trajectoryLaw {N : ℕ} (D : EulerData N) (S : SpinLaw)
    (T : ℕ) (z : Fin N → ℚ) (f : Point N → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂D.trajectoryLaw S T z) =
      ((D.operator S)^[T] f) (WithLp.toLp 2 (castV z)) := by
  rw [EulerData.trajectoryLaw, integral_map (measurable_of_finite _).aemeasurable hf.aestronglyMeasurable]
  rw [PMF.integral_eq_sum]
  have he := D.word_expectation S T z f
  simpa [PMF.uniformOfFintype_apply, ← Finset.mul_sum, one_div] using he

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











end CritWinSpin.Implementation.EulerAnalyticStep
end

end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.EulerPrecisionArithmetic





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

















end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open Matrix













end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CritWinSpin.LocalTM2.Compiled
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic



























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











end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessPSD
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled























end CritWinSpin.Implementation.PreprocessPSD
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessSelection
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessPSD













end CritWinSpin.Implementation.PreprocessSelection
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CritWinSpin.Implementation.PreprocessBranches
open Matrix CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessPSD PreprocessSelection















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













end CritWinSpin.Implementation.PreprocessIntegral
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.EulerFiniteBudget
open CritWinSpin.LocalTM2.Compiled EulerAnalyticStep PreprocessIntegral



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











 





theorem tv_triangle (p q r : Option A → ℝ) : tvDist p r ≤ tvDist p q + tvDist q r := by
  have hs := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => abs_sub_le (p z) (q z) (r z))
  rw [Finset.sum_add_distrib] at hs
  unfold tvDist
  linarith





















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































































end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic









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















end CritWinSpin.Implementation.SamplerDataFacts
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.SamplerBudgetBounds
open PreprocessIntegral PreprocessPSD





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



end CritWinSpin.Implementation.CriticalAnalyticTrial
end

end

section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CritWinSpin.Implementation.GibbsPerturbation

open IsingLTL.BeliefProp CritWinSpin.LocalTM2

















end CritWinSpin.Implementation.GibbsPerturbation
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled









end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled





















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









end CritWinSpin.Implementation.PreprocessCap
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.KernelPrecisionBudget
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessIntegral













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

































end CritWinSpin.Implementation.RetryPacketDecoding
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
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.LocalTM2.Compiled.SamplerCappedPath
open CritWinSpin.Implementation PreprocessPSD PreprocessSelection PreprocessBranches

 

 

 

 

 


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

def spinWeightApprox (S : SpinLaw) (t d : ℚ) (a : {a : ℚ // a ∈ S.A}) : ℚ :=
  enumeratedWeights (fun b : {a : ℚ // a ∈ S.A} => t * b.1)
    (fun b => S.ρ b.1) |t| d a

theorem spin_shift_max (S : SpinLaw) (t : ℚ) (a : {a : ℚ // a ∈ S.A}) : t * a.1 ≤ |t| := by
  have ha : |a.1| ≤ 1 := abs_le.mpr (S.mem_Icc a.1 a.2)
  calc
    _ ≤ |t * a.1| := le_abs_self _
    _ = |t| * |a.1| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
    _ = _ := mul_one _

theorem spin_pivot (S : SpinLaw) (t : ℚ) :
    ∃ a : {a : ℚ // a ∈ S.A}, t * a.1 = |t| ∧ S.ρ a.1 = S.ρ 1 := by
  by_cases ht : t < 0
  · refine ⟨⟨-1, S.neg_one_mem⟩, ?_, S.symm 1 S.one_mem⟩
    simp [abs_of_neg ht]
  · refine ⟨⟨1, S.one_mem⟩, ?_, rfl⟩
    simp [abs_of_nonneg (le_of_not_gt ht)]

theorem normalized_exp_eq_tilt (S : SpinLaw) (t : ℚ) :
    (fun a : {a : ℚ // a ∈ S.A} =>
      (Real.exp ((t * a.1 : ℚ) : ℝ) * (S.ρ a.1 : ℝ)) /
        ∑ b : {a : ℚ // a ∈ S.A}, Real.exp ((t * b.1 : ℚ) : ℝ) * (S.ρ b.1 : ℝ)) =
      (fun a => tilt S (t : ℝ) a.1) := by
  have hsum : (∑ b : {a : ℚ // a ∈ S.A}, Real.exp ((t * b.1 : ℚ) : ℝ) * (S.ρ b.1 : ℝ)) =
      mgf S (t : ℝ) := by
    rw [Finset.sum_coe_sort S.A (fun b : ℚ => Real.exp ((t * b : ℚ) : ℝ) * (S.ρ b : ℝ))]
    unfold mgf
    apply Finset.sum_congr rfl
    intro b _
    push_cast
    ring
  funext a
  rw [hsum]
  unfold tilt
  change Real.exp ((t * a.1 : ℚ) : ℝ) * (S.ρ a.1 : ℝ) / mgf S (t : ℝ) =
    (S.ρ a.1 : ℝ) * Real.exp ((t : ℝ) * (a.1 : ℝ) - Real.log (mgf S (t : ℝ)))
  rw [Real.exp_sub, Real.exp_log (mgf_pos S (t : ℝ))]
  push_cast
  ring

theorem spinWeightApprox_facts (S : SpinLaw) (t d : ℚ) (hd : 0 < d) (hd1 : d ≤ 1) :
    (∀ a, 0 ≤ spinWeightApprox S t d a) ∧
      (0 < ∑ a, spinWeightApprox S t d a) ∧
      tvDist (fun a => (spinWeightApprox S t d a : ℝ) / ∑ b, (spinWeightApprox S t d b : ℝ))
        (fun a => tilt S (t : ℝ) a.1) ≤
          (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ) := by
  obtain ⟨a, hmax, hρa⟩ := spin_pivot S t
  let E : {a : ℚ // a ∈ S.A} → ℚ := fun a => t * a.1
  let ρ : {a : ℚ // a ∈ S.A} → ℚ := fun a => S.ρ a.1
  have hρ : ∀ a, 0 < ρ a ∧ ρ a ≤ 1 := fun a =>
    ⟨S.pos a.1 a.2, (spin_weight_bounds S a.1 a.2).2⟩
  refine ⟨enumeratedWeights_nonneg E ρ |t| d hd hd1 (fun a => (hρ a).1.le)
    (spin_shift_max S t), ?_, ?_⟩
  · exact enumeratedWeights_sum_positive E ρ |t| d hd hd1 (fun a => (hρ a).1)
      (spin_shift_max S t) a hmax
  · have hh := enumeratedWeights_tv E ρ |t| d hd hd1 hρ (spin_shift_max S t) a hmax
    rw [normalized_exp_eq_tilt S t] at hh
    simpa only [ρ, hρa, E, spinWeightApprox] using hh

theorem alphabet_positive (S : SpinLaw) : 0 < (alphabet S).length := by
  have hh : (alphabet S) ≠ [] := by
    intro he
    have hm : (1 : ℚ) ∈ alphabet S := Finset.mem_toList.mpr S.one_mem
    rw [he] at hm
    simp at hm
  cases he : alphabet S with
  | nil => exact False.elim (hh he)
  | cons a as => simp

theorem alphabet_ofFn (S : SpinLaw) :
    alphabet S = List.ofFn (fun i => ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ)) := by
  apply List.ext_getElem <;> simp [alphabetEquiv_value]

theorem spinDrawWeights_correct (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ)
    (hc : 0 < C) (bits : List Bool) (fuel : List Unit)
    (hf : 2 / (spinPrecision C k : ℝ) ^ 3 + 2 ≤ fuel.length) :
    spinDrawWeights S C (((t, k), bits), fuel) =
      List.ofFn (fun i => spinWeightApprox S t (spinPrecision C k) (alphabetEquiv S i)) := by
  have hd : 0 < spinPrecision C k := by unfold spinPrecision; positivity
  unfold spinDrawWeights spinTable
  conv_lhs => rw [alphabet_ofFn S, List.map_ofFn, List.map_ofFn]
  congr 1
  funext i
  have habs : (if t < 0 then -t else t) = |t| := by
    by_cases ht : t < 0 <;> simp [ht, abs_of_neg, abs_of_nonneg, le_of_not_gt]
  rw [habs]
  change S.ρ ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ) *
    expWithFuel ((|t| - t * ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ), spinPrecision C k), fuel) = _
  rw [expWithFuel_eq_uniform _ _ (sub_nonneg.mpr (spin_shift_max S t (alphabetEquiv S i))) hd fuel hf]
  rfl

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp
noncomputable section

def indexSpinWeight (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ)
    (i : Fin (alphabet S).length) : ℚ :=
  spinWeightApprox S t (spinPrecision C k) (alphabetEquiv S i)

def indexSpinProb (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ)
    (i : Fin (alphabet S).length) : ℝ :=
  (indexSpinWeight S C t k i : ℝ) / ∑ j, (indexSpinWeight S C t k j : ℝ)

theorem spinPrecision_valid (C k : ℕ) (hC : 0 < C) :
    0 < spinPrecision C k ∧ spinPrecision C k ≤ 1 := by
  have hC1 : (1 : ℚ) ≤ C := by exact_mod_cast hC
  have hk1 : (1 : ℚ) ≤ (k : ℚ) + 1 := by have := Nat.cast_nonneg (α := ℚ) k; linarith
  have hden : 1 ≤ (C : ℚ) ^ 4 * ((k : ℚ) + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) hk1
  unfold spinPrecision
  exact ⟨by positivity, (div_le_one (by positivity)).mpr hden⟩

theorem indexSpinProb_facts (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) (hC : 0 < C) :
    IsDistribution (indexSpinProb S C t k) ∧
      tvDist (indexSpinProb S C t k)
        (fun i => tilt S (t : ℝ) ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ)) ≤
          ((alphabet S).length : ℝ) * spinPrecision C k / (S.ρ 1 : ℝ) := by
  obtain ⟨hd, hd1⟩ := spinPrecision_valid C k hC
  obtain ⟨hw, hW, htv⟩ := spinWeightApprox_facts S t (spinPrecision C k) hd hd1
  have hsumQ : (∑ i, indexSpinWeight S C t k i) = ∑ a, spinWeightApprox S t (spinPrecision C k) a :=
    Fintype.sum_equiv (alphabetEquiv S) _ _ (fun _ => rfl)
  have hsumR : (∑ i, (indexSpinWeight S C t k i : ℝ)) =
      ∑ a, (spinWeightApprox S t (spinPrecision C k) a : ℝ) := by exact_mod_cast hsumQ
  have hp : IsDistribution (indexSpinProb S C t k) := normalizedRational_distribution
    (indexSpinWeight S C t k) (fun i => hw (alphabetEquiv S i)) (by rw [hsumQ]; exact hW)
  refine ⟨hp, ?_⟩
  have he : indexSpinProb S C t k = fun i =>
      (spinWeightApprox S t (spinPrecision C k) (alphabetEquiv S i) : ℝ) /
        ∑ a, (spinWeightApprox S t (spinPrecision C k) a : ℝ) := by
    funext i
    rw [indexSpinProb, hsumR]
    rfl
  rw [he, tvDist_equiv (alphabetEquiv S)
    (fun a : {a : ℚ // a ∈ S.A} =>
      (spinWeightApprox S t (spinPrecision C k) a : ℝ) /
        ∑ b, (spinWeightApprox S t (spinPrecision C k) b : ℝ))
    (fun a => tilt S (t : ℝ) a.1)]
  have hc : Fintype.card {a : ℚ // a ∈ S.A} = (alphabet S).length := by simp [alphabet]
  simpa only [hc] using htv

def spinTicketCounts (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) : Fin (alphabet S).length → ℕ :=
  DyadicRounding.counts (indexSpinProb S C t k) (2 ^ spinBits S k) ⟨0, alphabet_positive S⟩

theorem spinTicketCounts_total (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) (hC : 0 < C) :
    ∑ i, spinTicketCounts S C t k i = 2 ^ spinBits S k :=
  DyadicRounding.counts_total _ (indexSpinProb_facts S C t k hC).1 _ _

theorem spinDraw_ofFn (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) (hC : 0 < C)
    (fuel : List Unit) (hf : 2 / (spinPrecision C k : ℝ) ^ 3 + 2 ≤ fuel.length)
    (ω : Fin (spinBits S k) → Bool) :
    spinDraw S C (((t, k), List.ofFn ω), fuel) =
      ((alphabetEquiv S (FiniteTicket.drawIndex (spinBits S k) (spinTicketCounts S C t k)
        (spinTicketCounts_total S C t k hC) ω) : {a : ℚ // a ∈ S.A}) : ℚ) := by
  have hw := spinDrawWeights_correct S C t k hC (List.ofFn ω) fuel hf
  have hv := sampleScalarTable_ofFn
    (fun i => ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ))
    (spinBits S k) (spinTicketCounts S C t k) (spinTicketCounts_total S C t k hC) ω
  rw [← alphabet_ofFn S] at hv
  unfold spinDraw
  rw [hw]
  change sampleScalarTable ((alphabet S,
    quantizedCounts (List.ofFn (indexSpinWeight S C t k), 2 ^ spinBits S k)),
      (List.ofFn ω).take (spinBits S k)) = _
  rw [quantizedCounts_ofFn_pos (alphabet_positive S)]
  have htape : (List.ofFn ω).take (spinBits S k) = List.ofFn ω := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn ω))
  rw [htape]
  exact hv

def spinWordLaw (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) (fuel : List Unit)
    (a : {a : ℚ // a ∈ S.A}) : ℝ :=
  (1 / (2 : ℝ) ^ spinBits S k) * ∑ ω : Fin (spinBits S k) → Bool,
    if spinDraw S C (((t, k), List.ofFn ω), fuel) = a.1 then (1 : ℝ) else 0

theorem spinWordLaw_eq (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) (hC : 0 < C)
    (fuel : List Unit) (hf : 2 / (spinPrecision C k : ℝ) ^ 3 + 2 ≤ fuel.length)
    (a : {a : ℚ // a ∈ S.A}) :
    spinWordLaw S C t k fuel a =
      (spinTicketCounts S C t k ((alphabetEquiv S).symm a) : ℝ) / (2 : ℝ) ^ spinBits S k := by
  have he (ω : Fin (spinBits S k) → Bool) :
      spinDraw S C (((t, k), List.ofFn ω), fuel) = a.1 ↔
        FiniteTicket.drawIndex (spinBits S k) (spinTicketCounts S C t k)
          (spinTicketCounts_total S C t k hC) ω = (alphabetEquiv S).symm a := by
    rw [spinDraw_ofFn S C t k hC fuel hf]
    rw [← Subtype.ext_iff, Equiv.apply_eq_iff_eq_symm_apply]
  unfold spinWordLaw
  simp_rw [he]
  exact FiniteTicket.drawIndex_law _ _ _ _

theorem spinWordLaw_distribution (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) (hC : 0 < C)
    (fuel : List Unit) (hf : 2 / (spinPrecision C k : ℝ) ^ 3 + 2 ≤ fuel.length) :
    IsDistribution (spinWordLaw S C t k fuel) := by
  have hq := DyadicRounding.law_distribution (indexSpinProb S C t k)
    (indexSpinProb_facts S C t k hC).1 (2 ^ spinBits S k) (by positivity) ⟨0, alphabet_positive S⟩
  refine ⟨fun a => by rw [spinWordLaw_eq S C t k hC fuel hf]; positivity, ?_⟩
  calc
    _ = ∑ i : Fin (alphabet S).length, spinWordLaw S C t k fuel (alphabetEquiv S i) :=
      (Fintype.sum_equiv (alphabetEquiv S) _ _ (fun _ => rfl)).symm
    _ = 1 := by
      simp_rw [spinWordLaw_eq S C t k hC fuel hf, Equiv.symm_apply_apply]
      simpa only [Nat.cast_pow, Nat.cast_ofNat, spinTicketCounts] using hq.2

theorem spinWordLaw_tv (S : SpinLaw) (C : ℕ) (t : ℚ) (k : ℕ) (hC : 0 < C)
    (fuel : List Unit) (hf : 2 / (spinPrecision C k : ℝ) ^ 3 + 2 ≤ fuel.length) :
    tvDist (spinWordLaw S C t k fuel) (fun a => tilt S (t : ℝ) a.1) ≤
      ((alphabet S).length : ℝ) * spinPrecision C k / (S.ρ 1 : ℝ) +
        ((alphabet S).length : ℝ) / (2 : ℝ) ^ spinBits S k := by
  have hp := (indexSpinProb_facts S C t k hC).1
  have hnom := (indexSpinProb_facts S C t k hC).2
  have hround := DyadicRounding.tv_error (indexSpinProb S C t k) hp
    (2 ^ spinBits S k) (by positivity) ⟨0, alphabet_positive S⟩
  rw [← tvDist_equiv (alphabetEquiv S)]
  have he : (fun i => spinWordLaw S C t k fuel (alphabetEquiv S i)) =
      fun i => (spinTicketCounts S C t k i : ℝ) / (2 : ℝ) ^ spinBits S k := by
    funext i
    rw [spinWordLaw_eq S C t k hC fuel hf, Equiv.symm_apply_apply]
  rw [he]
  have hh := tv_triangle (fun i => (spinTicketCounts S C t k i : ℝ) / (2 : ℝ) ^ spinBits S k)
    (indexSpinProb S C t k) (fun i => tilt S (t : ℝ) ((alphabetEquiv S i : {a : ℚ // a ∈ S.A}) : ℚ))
  have hr : tvDist (fun i => (spinTicketCounts S C t k i : ℝ) / (2 : ℝ) ^ spinBits S k)
      (indexSpinProb S C t k) ≤ ((alphabet S).length : ℝ) / (2 : ℝ) ^ spinBits S k := by
    simpa only [spinTicketCounts, Nat.cast_pow, Nat.cast_ofNat, Fintype.card_fin] using hround
  nlinarith

end
end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled
open IsingLTL.BeliefProp
noncomputable section

theorem clipProbability_bounds (p : ℚ) : 0 ≤ clipProbability p ∧ clipProbability p ≤ 1 := by
  unfold clipProbability
  split_ifs <;> constructor <;> linarith

theorem clipProbability_contracts (p : ℚ) (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    |(clipProbability p : ℝ) - q| ≤ |(p : ℝ) - q| := by
  unfold clipProbability
  split_ifs with hp hp
  · have hpR : (p : ℝ) < 0 := by exact_mod_cast hp
    rw [Rat.cast_zero, abs_of_nonpos (by linarith : 0 - q ≤ 0),
      abs_of_nonpos (by linarith : (p : ℝ) - q ≤ 0)]
    linarith
  · have hpR : (1 : ℝ) < p := by exact_mod_cast hp
    rw [Rat.cast_one, abs_of_nonneg (by linarith : 0 ≤ 1 - q),
      abs_of_nonneg (by linarith : 0 ≤ (p : ℝ) - q)]
    linarith
  · exact le_rfl

def binaryProb (p : ℚ) : Fin 2 → ℝ := ![(clipProbability p : ℝ), 1 - (clipProbability p : ℝ)]

theorem binaryProb_distribution (p : ℚ) : IsDistribution (binaryProb p) := by
  have hc := clipProbability_bounds p
  have hcR : 0 ≤ (clipProbability p : ℝ) ∧ (clipProbability p : ℝ) ≤ 1 := by exact_mod_cast hc
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [binaryProb] <;> linarith
  · simp [binaryProb, Fin.sum_univ_two]

def bernoulliCounts (p : ℚ) (k : ℕ) : Fin 2 → ℕ :=
  DyadicRounding.counts (binaryProb p) (2 ^ acceptanceBits k) 0

theorem bernoulliCounts_total (p : ℚ) (k : ℕ) :
    ∑ i, bernoulliCounts p k i = 2 ^ acceptanceBits k :=
  DyadicRounding.counts_total _ (binaryProb_distribution p) _ _

theorem bernoulliCounts_list (p : ℚ) (k : ℕ) :
    quantizedCounts ([clipProbability p, 1 - clipProbability p], 2 ^ acceptanceBits k) =
      List.ofFn (bernoulliCounts p k) := by
  have hh := quantizedCounts_ofFn ![clipProbability p, 1 - clipProbability p] (2 ^ acceptanceBits k)
  have hn : (fun i : Fin 2 => ((![(clipProbability p), 1 - clipProbability p] i : ℚ) : ℝ) /
      ∑ j : Fin 2, ((![(clipProbability p), 1 - clipProbability p] j : ℚ) : ℝ)) = binaryProb p := by
    funext i
    fin_cases i <;> simp [binaryProb, Fin.sum_univ_two]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.ofFn_const, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, hn, bernoulliCounts] using hh

theorem bernoulliDraw_ofFn (p : ℚ) (k : ℕ) (ω : Fin (acceptanceBits k) → Bool) :
    bernoulliDraw ((p, k), List.ofFn ω) =
      decide (FiniteTicket.drawIndex (acceptanceBits k) (bernoulliCounts p k)
        (bernoulliCounts_total p k) ω = 0) := by
  have hv := sampleScalarTable_ofFn (![1, 0] : Fin 2 → ℚ) (acceptanceBits k)
    (bernoulliCounts p k) (bernoulliCounts_total p k) ω
  have htape : (List.ofFn ω).take (acceptanceBits k) = List.ofFn ω := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn ω))
  unfold bernoulliDraw
  rw [htape]
  change decide (sampleScalarTable (([1, 0],
    quantizedCounts ([clipProbability p, 1 - clipProbability p], 2 ^ acceptanceBits k)), List.ofFn ω) = 1) = _
  rw [bernoulliCounts_list]
  have hvals : List.ofFn (![1, 0] : Fin 2 → ℚ) = [1, 0] := by decide
  rw [hvals] at hv
  rw [hv]
  congr 1
  have hpoint (i : Fin 2) : (![1, 0] : Fin 2 → ℚ) i = 1 ↔ i = 0 := by
    fin_cases i <;> norm_num
  exact propext (hpoint _)

def bernoulliWordProb (p : ℚ) (k : ℕ) : ℝ :=
  (1 / (2 : ℝ) ^ acceptanceBits k) *
    ∑ ω : Fin (acceptanceBits k) → Bool, if bernoulliDraw ((p, k), List.ofFn ω) then (1 : ℝ) else 0

theorem bernoulliWordProb_eq (p : ℚ) (k : ℕ) :
    bernoulliWordProb p k = (bernoulliCounts p k 0 : ℝ) / (2 : ℝ) ^ acceptanceBits k := by
  unfold bernoulliWordProb
  simp_rw [bernoulliDraw_ofFn, decide_eq_true_eq]
  exact FiniteTicket.drawIndex_law _ _ _ _



theorem bernoulliWordProb_error (p : ℚ) (k : ℕ) :
    |bernoulliWordProb p k - (clipProbability p : ℝ)| ≤ 4 / (2 : ℝ) ^ acceptanceBits k := by
  have ht := DyadicRounding.tv_error (binaryProb p) (binaryProb_distribution p)
    (2 ^ acceptanceBits k) (by positivity) 0
  have hp := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.univ) => abs_nonneg
      ((bernoulliCounts p k i : ℝ) / (2 : ℝ) ^ acceptanceBits k - binaryProb p i))
    (Finset.mem_univ (0 : Fin 2))
  rw [bernoulliWordProb_eq]
  change |(bernoulliCounts p k 0 : ℝ) / (2 : ℝ) ^ acceptanceBits k - (clipProbability p : ℝ)| ≤ _
  change |(bernoulliCounts p k 0 : ℝ) / (2 : ℝ) ^ acceptanceBits k - (clipProbability p : ℝ)| ≤ _ at hp
  unfold tvDist at ht
  simp only [Nat.cast_pow, Nat.cast_ofNat, Fintype.card_fin] at ht
  change (∑ i, |(bernoulliCounts p k i : ℝ) / (2 : ℝ) ^ acceptanceBits k - binaryProb p i|) / 2 ≤
    (2 : ℝ) / (2 : ℝ) ^ acceptanceBits k at ht
  have hsum : (∑ i, |(bernoulliCounts p k i : ℝ) / (2 : ℝ) ^ acceptanceBits k - binaryProb p i|) ≤
      4 / (2 : ℝ) ^ acceptanceBits k := by
    have hh := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp ht
    have heq : ((2 : ℝ) / (2 : ℝ) ^ acceptanceBits k) * 2 = 4 / (2 : ℝ) ^ acceptanceBits k := by ring
    rw [heq] at hh
    exact hh
  exact hp.trans hsum

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





theorem EulerData.kernelFields_ofFn {N : ℕ} (D : EulerData N) (z : Fin N → ℚ) (bits : List Bool) :
    kernelFields (D.kernelInput z bits) = List.ofFn (D.fields z) := by
  unfold kernelFields driftArguments EulerData.kernelInput EulerData.context EulerData.fields
  rw [matrixVector_ofFn, zip_ofFn, List.map_ofFn]
  rfl

theorem EulerData.kernelAcceptance_independent {N : ℕ} (S : SpinLaw) (D : EulerData N)
    (z : Fin N → ℚ) (bits : List Bool) :
    kernelAcceptance S (D.kernelInput z bits) = kernelAcceptance S (D.kernelInput z []) := by
  unfold kernelAcceptance kernelIntegralSum
  rw [D.kernelFields_ofFn z bits, D.kernelFields_ofFn z []]
  rfl

def kernelPacket {N : ℕ} (S : SpinLaw) (k : ℕ)
    (a : Fin (acceptanceBits k) → Bool) (w : Fin N → Fin (spinBits S k) → Bool) : List Bool :=
  List.ofFn a ++ (List.ofFn (fun i => List.ofFn (w i))).flatten



theorem kernelPacket_take {N : ℕ} (S : SpinLaw) (k : ℕ)
    (a : Fin (acceptanceBits k) → Bool) (w : Fin N → Fin (spinBits S k) → Bool) :
    (kernelPacket S k a w).take (acceptanceBits k) = List.ofFn a := by
  exact List.take_left' (by simp only [List.length_ofFn])

theorem kernelPacket_drop {N : ℕ} (S : SpinLaw) (k : ℕ)
    (a : Fin (acceptanceBits k) → Bool) (w : Fin N → Fin (spinBits S k) → Bool) :
    (kernelPacket S k a w).drop (acceptanceBits k) =
      (List.ofFn (fun i => List.ofFn (w i))).flatten := by
  exact List.drop_left' (by simp only [List.length_ofFn])

theorem spinPacket_block {N : ℕ} (S : SpinLaw) (k : ℕ)
    (w : Fin N → Fin (spinBits S k) → Bool) (i : Fin N) :
    bitBlock (((List.ofFn (fun i => List.ofFn (w i))).flatten, spinBits S k), i.val) = List.ofFn (w i) := by
  have hr : ∀ row ∈ List.ofFn (fun i => List.ofFn (w i)), row.length = spinBits S k := by
    intro row hrow
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hrow
    simp only [List.length_ofFn]
  have hh := flattened_block (List.ofFn (fun i => List.ofFn (w i))) (spinBits S k) hr [] i.val
    (by simpa only [List.length_ofFn] using i.isLt)
  simpa only [List.append_nil, List.getElem_ofFn, bitBlock] using hh

def spinTyped (S : SpinLaw) (C : ℕ) (hC : 0 < C) (t : ℚ) (k : ℕ)
    (w : Fin (spinBits S k) → Bool) : {a : ℚ // a ∈ S.A} :=
  alphabetEquiv S (FiniteTicket.drawIndex (spinBits S k) (spinTicketCounts S C t k)
    (spinTicketCounts_total S C t k hC) w)

theorem kernelSpinValues_packet {N : ℕ} (S : SpinLaw) (C : ℕ) (hC : 0 < C)
    (D : EulerData N) (z : Fin N → ℚ)
    (hf : 2 / (spinPrecision C D.k : ℝ)^3 + 2 ≤ D.fuel.length)
    (a : Fin (acceptanceBits D.k) → Bool) (w : Fin N → Fin (spinBits S D.k) → Bool) :
    kernelSpinValues S C (D.kernelInput z (kernelPacket S D.k a w)) =
      List.ofFn (fun i => (spinTyped S C hC (D.fields z i) D.k (w i) : ℚ)) := by
  unfold kernelSpinValues
  rw [D.kernelFields_ofFn]
  change (siteNumbers (List.replicate N ())).map (fun i => spinDraw S C
    (((((List.ofFn (D.fields z))[i]?).getD 0, D.k),
      bitBlock (((kernelPacket S D.k a w).drop (acceptanceBits D.k), spinBits S D.k), i)), D.fuel)) = _
  rw [kernelPacket_drop]
  simp only [siteNumbers, List.length_replicate]
  rw [map_range_eq_ofFn]
  congr 1
  funext i
  simp only [List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  rw [spinPacket_block]
  exact spinDraw_ofFn S C (D.fields z i) D.k hC D.fuel hf (w i)

theorem kernelOutput_packet {N : ℕ} (S : SpinLaw) (C : ℕ) (hC : 0 < C)
    (D : EulerData N) (z : Fin N → ℚ)
    (hf : 2 / (spinPrecision C D.k : ℝ)^3 + 2 ≤ D.fuel.length)
    (a : Fin (acceptanceBits D.k) → Bool) (w : Fin N → Fin (spinBits S D.k) → Bool) :
    kernelOutput S C (D.kernelInput z (kernelPacket S D.k a w)) =
      if bernoulliDraw ((kernelAcceptance S (D.kernelInput z []), D.k), List.ofFn a) then
        encConfig (fun i => spinTyped S C hC (D.fields z i) D.k (w i)) else [] := by
  unfold kernelOutput
  rw [D.kernelAcceptance_independent S z, kernelSpinValues_packet S C hC D z hf a w]
  change (if bernoulliDraw ((kernelAcceptance S (D.kernelInput z []), D.k),
    (kernelPacket S D.k a w).take (acceptanceBits D.k)) then _ else _) = _
  rw [kernelPacket_take, ofFn_flatMap]
  rfl

end
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
set_option backward.isDefEq.respectTransparency false
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

namespace CritWinSpin.LocalTM2.FiniteDraw
open IsingLTL.BeliefProp Classical
noncomputable section









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



theorem accept {U W A : Type} [Fintype U] [Nonempty U] [Fintype W] [Nonempty W] [Fintype A]
    (b : U → Bool) (draw : W → A) :
    law (fun ω : U × W => if b ω.1 then some (draw ω.2) else none) =
      CritWinSpin.Implementation.FiniteRetry.trial (law draw)
        ((1 / (Fintype.card U : ℝ)) * ∑ u, if b u then (1 : ℝ) else 0) := by
  funext x
  have hc : (Fintype.card W : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card W ≠ 0)
  have hcu : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card U ≠ 0)
  cases x with
  | none =>
    have hp (u : U) (w : W) :
        (if (if b u then some (draw w) else none) = none then (1 : ℝ) else 0) =
          1 - (if b u then (1 : ℝ) else 0) := by cases h : b u <;> simp [h]
    unfold law CritWinSpin.Implementation.FiniteRetry.trial
    simp_rw [Fintype.sum_prod_type, hp]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    field_simp [hc, hcu]
  | some x =>
    have hp (u : U) (w : W) :
        (if (if b u then some (draw w) else none) = some x then (1 : ℝ) else 0) =
          (if b u then (1 : ℝ) else 0) * (if draw w = x then (1 : ℝ) else 0) := by
      cases h : b u <;> simp [h]
    unfold law CritWinSpin.Implementation.FiniteRetry.trial
    simp_rw [Fintype.sum_prod_type, hp, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
    simp only [Fintype.card_prod, Nat.cast_mul]
    ring

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



theorem product_distribution {n : ℕ} (p : Fin n → A → ℝ) (hp : ∀ i, IsDistribution (p i)) :
    IsDistribution (productLaw p) := by
  constructor
  · intro xs; exact Finset.prod_nonneg (fun i _ => (hp i).1 (xs i))
  · simp only [productLaw, ← Fintype.prod_sum, fun i => (hp i).2, Finset.prod_const_one]

theorem pair_product_tv {X Y : Type} [Fintype X] [Fintype Y]
    (p q : X → ℝ) (r s : Y → ℝ)
    (hq : IsDistribution q) (hr : IsDistribution r) :
    tvDist (fun z : X × Y => p z.1 * r z.2) (fun z => q z.1 * s z.2) ≤
      tvDist p q + tvDist r s := by
  have hpoint (x : X) (y : Y) : |p x * r y - q x * s y| ≤
      |p x - q x| * r y + q x * |r y - s y| := by
    calc
      _ = |(p x - q x) * r y + q x * (r y - s y)| := by congr 1; ring
      _ ≤ |(p x - q x) * r y| + |q x * (r y - s y)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hr.1 y), abs_of_nonneg (hq.1 x)]
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hpoint x y))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hq.2, hr.2,
    mul_one, one_mul] at hs
  unfold tvDist
  rw [Fintype.sum_prod_type]
  linarith only [hs]

theorem product_tv {n : ℕ} (p q : Fin n → A → ℝ)
    (hp : ∀ i, IsDistribution (p i)) (hq : ∀ i, IsDistribution (q i)) :
    tvDist (productLaw p) (productLaw q) ≤ ∑ i, tvDist (p i) (q i) := by
  classical
  induction n with
  | zero => simp [tvDist, productLaw]
  | succ n ih =>
    have ht := pair_product_tv (p 0) (q 0)
      (productLaw (fun i : Fin n => p i.succ)) (productLaw (fun i : Fin n => q i.succ))
      (hq 0) (product_distribution _ (fun i => hp i.succ))
    have hi := ih (fun i => p i.succ) (fun i => q i.succ)
      (fun i => hp i.succ) (fun i => hq i.succ)
    have he : tvDist (productLaw p) (productLaw q) =
        tvDist (fun z : A × (Fin n → A) => p 0 z.1 * productLaw (fun i => p i.succ) z.2)
          (fun z => q 0 z.1 * productLaw (fun i => q i.succ) z.2) := by
      have hh := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => A))
        (fun xs => |productLaw p xs - productLaw q xs|)
      unfold tvDist
      rw [← hh]
      simp only [productLaw, Fin.prod_univ_succ, Fin.consEquiv, Equiv.coe_fn_mk,
        Fin.cons_zero, Fin.cons_succ]
    rw [he, Fin.sum_univ_succ]
    linarith only [ht, hi]

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

theorem kernel_error {n : ℕ} (p q : Fin n → A → ℝ)
    (hp : ∀ i, IsDistribution (p i)) (hq : ∀ i, IsDistribution (q i))
    {a b ηa : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (η : Fin n → ℝ)
    (ha : |a - b| ≤ ηa) (he : ∀ i, tvDist (p i) (q i) ≤ η i) :
    tvDist (FiniteRetry.trial (productLaw p) a) (FiniteRetry.trial (productLaw q) b) ≤ ηa + ∑ i, η i := by
  exact (trial_tv _ _ (product_distribution p hp) hb hb1).trans
    (add_le_add ha ((product_tv p q hp hq).trans (Finset.sum_le_sum (fun i _ => he i))))

end CritWinSpin.Implementation.FiniteKernelTV
end

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.KernelAcceptance
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled PreprocessIntegral

theorem envelopeValue_nonneg (S : SpinLaw) (u : EnvelopeInput × ℕ) : 0 ≤ envelopeValue S u := by
  dsimp only [envelopeValue]
  split_ifs with h
  · exact h
  · exact le_rfl

theorem envelopeWithFuel_nonneg (S : SpinLaw) (u : EnvelopeInput) : 0 ≤ envelopeWithFuel S u := by
  have hm : 0 ≤ envelopeMesh u := by
    unfold envelopeMesh
    rw [envelopeLeft_eq]
    exact div_nonneg (sub_nonneg.mpr (min_le_right _ _)) (Nat.cast_nonneg _)
  unfold envelopeWithFuel
  apply mul_nonneg hm
  apply List.sum_nonneg
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact envelopeValue_nonneg S _

theorem uniform_envelope_error (S : SpinLaw) (hS : IsGHS S) (s t d : ℚ)
    (grid fuel : List Unit) (hs : tau S < (s : ℝ)) (hn : 0 < grid.length)
    (hdR : (d : ℝ) = 1 / (grid.length : ℝ))
    (hf : 2 / (d : ℝ)^3 + 2 ≤ (fuel.length : ℝ)) :
    |(envelopeWithFuel S (((s,t,d),grid),fuel) : ℝ) - ds S (s:ℝ) (t:ℝ)| ≤
      ((s:ℝ)^2 + (s:ℝ) + spinErrorCoefficient S * (s:ℝ)) / (grid.length:ℝ) := by
  have hnr : (0:ℝ) < grid.length := by exact_mod_cast hn
  have hspos := (EnvelopeAnalysis.tau_pos S).trans hs
  have hsQ : 0 < s := by exact_mod_cast hspos
  have hd : 0 < d := by
    have hh : (0:ℝ) < d := by rw [hdR]; positivity
    exact_mod_cast hh
  have hd1 : d ≤ 1 := by
    have hh : (d:ℝ) ≤ 1 := by
      rw [hdR]
      exact (div_le_one hnr).2 (by exact_mod_cast hn)
    exact_mod_cast hh
  have hr := envelopeWithFuel_error S hS s t d hs grid fuel hn hd hd1 hf
  rw [← EnvelopeIntegral.discrepancy_eq S (s:ℝ) (t:ℝ)] at hr
  let hq := envelopeMesh (((s,t,d),grid),fuel)
  have ha : 0 ≤ envelopeLeft (s,t) ∧ envelopeLeft (s,t) ≤ s := by
    rw [envelopeLeft_eq]
    exact ⟨le_min (abs_nonneg t) hsQ.le, min_le_right _ _⟩
  have hq0 : 0 ≤ hq := div_nonneg (sub_nonneg.mpr ha.2) (Nat.cast_nonneg _)
  have hqu : hq ≤ s / (grid.length : ℚ) :=
    div_le_div_of_nonneg_right (sub_le_self s ha.1) (Nat.cast_nonneg _)
  have h0 : (0:ℝ) ≤ hq := by exact_mod_cast hq0
  have hu : (hq:ℝ) ≤ (s:ℝ)/(grid.length:ℝ) := by exact_mod_cast hqu
  have hρ : (0:ℝ) < S.ρ 1 := by exact_mod_cast S.pos 1 S.one_mem
  have h₁ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hu 2)
    (show (0:ℝ) ≤ 1+1/(s:ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hu
    (show (0:ℝ) ≤ 2 * (Fintype.card {x : ℚ // x ∈ S.A} : ℝ) * (d:ℝ) / (S.ρ 1 : ℝ) by positivity)
  have hsum := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hnr.le
  have hFactor : (grid.length:ℝ) *
      ((1+1/(s:ℝ))*((s:ℝ)/(grid.length:ℝ))^2 + ((s:ℝ)/(grid.length:ℝ))*
        (2*(Fintype.card {x : ℚ // x ∈ S.A}:ℝ)*(d:ℝ)/(S.ρ 1:ℝ))) =
      ((s:ℝ)^2+(s:ℝ)+spinErrorCoefficient S*(s:ℝ))/(grid.length:ℝ) := by
    rw [hdR]
    unfold spinErrorCoefficient
    field_simp [hspos.ne', hnr.ne', hρ.ne'] <;> ring
  rw [hFactor] at hsum
  exact hr.trans hsum

theorem expneg_difference_le {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    Real.exp (-y) - Real.exp (-x) ≤ x-y := by
  have hgap := Real.add_one_le_exp (-(x-y))
  have hpos : 0 ≤ 1-Real.exp (-(x-y)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith only [hyx]))
  have hweight : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)
  have he : Real.exp (-y) - Real.exp (-x) = Real.exp (-y) * (1-Real.exp (-(x-y))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  have hh := mul_le_mul hweight (show 1-Real.exp (-(x-y)) ≤ x-y by linarith only [hgap])
    hpos zero_le_one
  simpa only [one_mul] using hh

theorem expneg_lipschitz {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x-y| := by
  rcases le_total x y with hxy | hyx
  · have hh := expneg_difference_le hx hxy
    have he := Real.exp_le_exp.mpr (neg_le_neg hxy)
    rw [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith only [hh]
  · have hh := expneg_difference_le hy hyx
    have he := Real.exp_le_exp.mpr (neg_le_neg hyx)
    rw [abs_of_nonpos (sub_nonpos.mpr he), abs_of_nonneg (sub_nonneg.mpr hyx)]
    linarith only [hh]

theorem sum_error {X : Type*} (xs : List X) (f g : X → ℝ) (E : ℝ)
    (he : ∀ x, |f x-g x| ≤ E) :
    |(xs.map f).sum - (xs.map g).sum| ≤ (xs.length:ℝ)*E := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ht := abs_add_le (f x-g x) ((xs.map f).sum-(xs.map g).sum)
    have hid : f x + (xs.map f).sum - (g x+(xs.map g).sum) =
        (f x-g x)+((xs.map f).sum-(xs.map g).sum) := by ring
    rw [hid]
    nlinarith only [ht, he x, ih]

theorem rational_sum_map (xs : List ℚ) (f : ℚ → ℚ) :
    ((xs.map f).sum : ℝ) = (xs.map (fun t => (f t : ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons t xs ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih]

def trueGap (S : SpinLaw) (u : KernelInput) : ℝ :=
  ((kernelFields u).map (fun (t : ℚ) => ds S (u.1.1.1.2.2.1 : ℝ) (t:ℝ))).sum

theorem kernelAcceptance_error (S : SpinLaw) (hS : IsGHS S) (u : KernelInput)
    (hs : tau S < (u.1.1.1.2.2.1 : ℝ))
    (hTake : u.1.1.2+1 ≤ u.2.length)
    (hf : 2 / (1/((u.1.1.2:ℝ)+1))^3 + 2 ≤ (u.2.length:ℝ)) :
    |(kernelAcceptance S u : ℝ) - Real.exp (-trueGap S u)| ≤
      (1+(kernelFields u).length *
        ((u.1.1.1.2.2.1:ℝ)^2+(u.1.1.1.2.2.1:ℝ)+
          spinErrorCoefficient S*(u.1.1.1.2.2.1:ℝ))) / ((u.1.1.2:ℝ)+1) := by
  let s := u.1.1.1.2.2.1
  let d : ℚ := 1/((u.1.1.2:ℚ)+1)
  let grid := u.2.take (u.1.1.2+1)
  let f : ℚ → ℚ := fun t => envelopeWithFuel S (((s,t,d),grid),u.2)
  let F : ℝ := (s:ℝ)^2+(s:ℝ)+spinErrorCoefficient S*(s:ℝ)
  have hGrid : grid.length = u.1.1.2+1 := by simp only [grid, List.length_take, Nat.min_eq_left hTake]
  have hn : 0 < grid.length := by rw [hGrid]; omega
  have hdR : (d:ℝ) = 1/(grid.length:ℝ) := by rw [hGrid]; dsimp [d]; push_cast; rfl
  have herr (t : ℚ) : |(f t:ℝ)-ds S (s:ℝ) (t:ℝ)| ≤ F/(grid.length:ℝ) :=
    uniform_envelope_error S hS s t d grid u.2 hs hn hdR (by dsimp [d]; push_cast; exact hf)
  have hIntegral : (kernelIntegralSum S u:ℝ) = ((kernelFields u).map (fun t => (f t:ℝ))).sum :=
    rational_sum_map (kernelFields u) f
  have hsum := sum_error (kernelFields u) (fun t => (f t:ℝ)) (fun t => ds S (s:ℝ) (t:ℝ))
    (F/(grid.length:ℝ)) herr
  rw [← hIntegral] at hsum
  have hsumTrue : |(kernelIntegralSum S u:ℝ)-trueGap S u| ≤
      (kernelFields u).length*(F/(grid.length:ℝ)) := by
    simpa only [trueGap, s] using hsum
  have hNonnegQ : 0 ≤ kernelIntegralSum S u := by
    unfold kernelIntegralSum
    apply List.sum_nonneg
    intro x hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact envelopeWithFuel_nonneg S _
  have hNonnegR : (0:ℝ) ≤ kernelIntegralSum S u := by exact_mod_cast hNonnegQ
  have hGap : 0 ≤ trueGap S u := by
    unfold trueGap
    apply List.sum_nonneg
    intro x hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact EnvelopeAnalysis.ds_nonneg S hS hs _
  have hExp := expneg_lipschitz hNonnegR hGap
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d]
    apply (div_le_one (by positivity : (0:ℚ) < (u.1.1.2:ℚ)+1)).2
    have hh : (0:ℚ) ≤ u.1.1.2 := Nat.cast_nonneg _
    linarith only [hh]
  have hAlg := expNegativeApprox_error (kernelIntegralSum S u) d hNonnegQ hd hd1
  have hCode := expWithFuel_eq_uniform (kernelIntegralSum S u) d hNonnegQ hd u.2
    (by dsimp [d]; push_cast; exact hf)
  have hApprox : |(kernelAcceptance S u:ℝ)-Real.exp (-(kernelIntegralSum S u:ℝ))| ≤ (d:ℝ) := by
    change |(expWithFuel ((kernelIntegralSum S u,d),u.2):ℝ)-Real.exp (-(kernelIntegralSum S u:ℝ))| ≤ _
    rw [hCode]
    exact hAlg.2
  have ht := abs_sub_le (kernelAcceptance S u:ℝ) (Real.exp (-(kernelIntegralSum S u:ℝ))) (Real.exp (-trueGap S u))
  rw [hGrid] at hsumTrue
  have hdCast : (d:ℝ) = 1/((u.1.1.2:ℝ)+1) := by dsimp [d]; push_cast; rfl
  rw [hdCast] at hApprox
  have hFinal : 1/((u.1.1.2:ℝ)+1)+(kernelFields u).length*(F/((u.1.1.2:ℝ)+1)) =
      (1+(kernelFields u).length*F)/((u.1.1.2:ℝ)+1) := by ring
  have hs' : |(kernelIntegralSum S u:ℝ)-trueGap S u| ≤
      (kernelFields u).length*(F/((u.1.1.2:ℝ)+1)) := by simpa only [Nat.cast_add, Nat.cast_one] using hsumTrue
  exact (ht.trans (add_le_add hApprox (hExp.trans hs'))).trans_eq hFinal

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

def kernelPacketEquiv (S : SpinLaw) (N k : ℕ) :
    ((Fin (acceptanceBits k) → Bool) × (Fin N → Fin (spinBits S k) → Bool)) ≃
      (Fin (acceptanceBits k + N * spinBits S k) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (splitBitEquiv N (spinBits S k)).symm).trans
    (Fin.appendEquiv (acceptanceBits k) (N * spinBits S k))

theorem kernelPacketEquiv_list {N : ℕ} (S : SpinLaw) (k : ℕ)
    (a : Fin (acceptanceBits k) → Bool) (w : Fin N → Fin (spinBits S k) → Bool) :
    List.ofFn (kernelPacketEquiv S N k (a,w)) = kernelPacket S k a w := by
  change List.ofFn (Fin.append a ((splitBitEquiv N (spinBits S k)).symm w)) = _
  rw [List.ofFn_fin_append, List.ofFn_mul]
  unfold kernelPacket
  apply congrArg (fun rows : List (List Bool) => List.ofFn a ++ rows.flatten)
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hh := congrFun (congrFun ((splitBitEquiv N (spinBits S k)).apply_symm_apply w) i) j
  simpa only [splitBitEquiv_apply, blockIndex] using hh

theorem spinTyped_law (S : SpinLaw) (C : ℕ) (hC : 0 < C) (t : ℚ) (k : ℕ)
    (fuel : List Unit) (hf : 2 / (spinPrecision C k : ℝ)^3 + 2 ≤ fuel.length) :
    FiniteDraw.law (spinTyped S C hC t k) = spinWordLaw S C t k fuel := by
  funext a
  unfold FiniteDraw.law spinWordLaw
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  rw [spinDraw_ofFn S C t k hC fuel hf]
  congr 1
  exact propext Subtype.ext_iff



theorem kernelWordLaw_eq {N : ℕ} (S : SpinLaw) (C : ℕ) (hC : 0 < C)
    (D : EulerData N) (z : Fin N → ℚ)
    (hf : 2 / (spinPrecision C D.k : ℝ)^3 + 2 ≤ D.fuel.length)
    (hnil : decConfig S N [] = none) :
    kernelWordLaw S C D z = CritWinSpin.Implementation.FiniteRetry.trial
      (CritWinSpin.Implementation.FiniteKernelTV.productLaw
        (fun i => spinWordLaw S C (D.fields z i) D.k D.fuel))
      (bernoulliWordProb (kernelAcceptance S (D.kernelInput z [])) D.k) := by
  let draw := fun w : Fin (acceptanceBits D.k + N * spinBits S D.k) → Bool =>
    decConfig S N (kernelOutput S C (D.kernelInput z (List.ofFn w)))
  have he := FiniteDraw.source_equiv (kernelPacketEquiv S N D.k) draw
  have hd : draw ∘ kernelPacketEquiv S N D.k =
      fun aw => if bernoulliDraw ((kernelAcceptance S (D.kernelInput z []),D.k),List.ofFn aw.1)
        then some (fun i => spinTyped S C hC (D.fields z i) D.k (aw.2 i)) else none := by
    funext aw
    dsimp only [draw, Function.comp_def]
    rw [kernelPacketEquiv_list, kernelOutput_packet S C hC D z hf]
    split_ifs
    · exact decConfig_encConfig _
    · exact hnil
  rw [hd] at he
  have haccept := FiniteDraw.accept
    (fun a : Fin (acceptanceBits D.k) → Bool =>
      bernoulliDraw ((kernelAcceptance S (D.kernelInput z []),D.k),List.ofFn a))
    (fun w : Fin N → Fin (spinBits S D.k) → Bool =>
      fun i => spinTyped S C hC (D.fields z i) D.k (w i))
  rw [haccept] at he
  have hp : FiniteDraw.law (fun w : Fin N → Fin (spinBits S D.k) → Bool =>
      fun i => spinTyped S C hC (D.fields z i) D.k (w i)) =
      CritWinSpin.Implementation.FiniteKernelTV.productLaw
        (fun i => spinWordLaw S C (D.fields z i) D.k D.fuel) := by
    funext x
    rw [FiniteDraw.product]
    unfold CritWinSpin.Implementation.FiniteKernelTV.productLaw
    congr 1
    funext i
    rw [spinTyped_law S C hC (D.fields z i) D.k D.fuel hf]
  rw [hp] at he
  have hc : (1 / (Fintype.card (Fin (acceptanceBits D.k) → Bool) : ℝ)) *
      (∑ w : Fin (acceptanceBits D.k) → Bool, if bernoulliDraw ((kernelAcceptance S (D.kernelInput z []),D.k),List.ofFn w)
        then (1 : ℝ) else 0) = bernoulliWordProb (kernelAcceptance S (D.kernelInput z [])) D.k := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat, bernoulliWordProb]
  rw [hc] at he
  exact he.symm




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







theorem tv_mean {W A : Type} [Fintype W] [Nonempty W] [Fintype A]
    (p q : W → A → ℝ) {η : ℝ} (he : ∀ w, tvDist (p w) (q w) ≤ η) :
    tvDist (fun a => mean (fun w => p w a)) (fun a => mean (fun w => q w a)) ≤ η := by
  have hc : 0 < (Fintype.card W : ℝ) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card W)
  have hc0 : (Fintype.card W : ℝ) ≠ 0 := ne_of_gt hc
  have hp (a : A) : |mean (fun w => p w a) - mean (fun w => q w a)| ≤
      (1 / (Fintype.card W : ℝ)) * ∑ w, |p w a - q w a| := by
    unfold mean
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ 1 / (Fintype.card W : ℝ))]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hp a)
  have htot : (1 / (Fintype.card W : ℝ)) * ∑ w, ∑ a, |p w a - q w a| ≤ 2 * η := by
    have hh := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) =>
      (show (∑ a, |p w a - q w a|) ≤ 2 * η by
        have := he w; unfold tvDist at this; linarith))
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1 / (Fintype.card W : ℝ) by positivity)
    simpa [hc0] using hh'
  rw [← Finset.mul_sum, Finset.sum_comm] at hs
  unfold tvDist
  linarith only [hs, htot]

end
end CritWinSpin.LocalTM2.FiniteDraw

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option Elab.async false

namespace CritWinSpin.LocalTM2.Compiled.GenericPacketLaw









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

theorem EulerData.fields_cast {N : ℕ} (D : EulerData N) (z : Fin N → ℚ) (i : Fin N) :
    (D.fields z i : ℝ) = (castM D.L).mulVec (castV z) i + castV D.h i := by
  simp only [EulerData.fields, Matrix.mulVec, dotProduct, castM, castV,
    Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Matrix.map_apply]

theorem kernelWordLaw_tv {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C : ℕ) (hC : 0 < C)
    (D : EulerData N) (z : Fin N → ℚ) (hs : tau S < (D.sCap : ℝ))
    (hfSpin : 2 / (spinPrecision C D.k : ℝ)^3 + 2 ≤ D.fuel.length)
    (hTake : D.k+1 ≤ D.fuel.length)
    (hf : 2 / (1/((D.k:ℝ)+1))^3 + 2 ≤ (D.fuel.length:ℝ))
    (hnil : decConfig S N [] = none) :
    tvDist (kernelWordLaw S C D z) (kernelK S (D.sCap:ℝ) (castM D.L) (castV D.h) (castV z)) ≤
      KernelPrecisionBudget.error S C N D.k (D.sCap:ℝ) := by
  let q := fun i : Fin N => fun a : {a : ℚ // a ∈ S.A} => tilt S (D.fields z i : ℝ) a.1
  let p := fun i : Fin N => spinWordLaw S C (D.fields z i) D.k D.fuel
  let b := Real.exp (-(∑ i, ds S (D.sCap:ℝ) (D.fields z i : ℝ)))
  let a := bernoulliWordProb (kernelAcceptance S (D.kernelInput z [])) D.k
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hb1 : b ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (Finset.sum_nonneg (fun i _ => EnvelopeAnalysis.ds_nonneg S hS hs _)))
  have hq : ∀ i, IsDistribution (q i) := fun i =>
    ⟨SpinKernel.tilt_nonneg S _, SpinKernel.tilt_sum_one S _⟩
  have hp : ∀ i, IsDistribution (p i) := fun i =>
    spinWordLaw_distribution S C (D.fields z i) D.k hC D.fuel hfSpin
  have hgap : KernelAcceptance.trueGap S (D.kernelInput z []) =
      ∑ i, ds S (D.sCap:ℝ) (D.fields z i : ℝ) := by
    unfold KernelAcceptance.trueGap
    rw [D.kernelFields_ofFn]
    simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn, EulerData.kernelInput, EulerData.context]
  have he := KernelAcceptance.kernelAcceptance_error S hS (D.kernelInput z []) hs hTake hf
  rw [hgap, D.kernelFields_ofFn] at he
  simp only [List.length_ofFn] at he
  change |(kernelAcceptance S (D.kernelInput z []):ℝ)-b| ≤
    (1+(N:ℝ)*((D.sCap:ℝ)^2+(D.sCap:ℝ)+PreprocessIntegral.spinErrorCoefficient S*(D.sCap:ℝ)))/((D.k:ℝ)+1) at he
  have ha : |a-b| ≤
      (1+(N:ℝ)*((D.sCap:ℝ)^2+(D.sCap:ℝ)+PreprocessIntegral.spinErrorCoefficient S*(D.sCap:ℝ)))/((D.k:ℝ)+1)+
      4/(2:ℝ)^acceptanceBits D.k := by
    have hround := bernoulliWordProb_error (kernelAcceptance S (D.kernelInput z [])) D.k
    have hclip := clipProbability_contracts (kernelAcceptance S (D.kernelInput z [])) b ⟨hb0,hb1⟩
    have ht := abs_sub_le a (clipProbability (kernelAcceptance S (D.kernelInput z [])):ℝ) b
    dsimp only [a] at ht ⊢
    linarith only [ht,hround,hclip,he]
  have htv := FiniteKernelTV.kernel_error p q hp hq hb0 hb1
    (fun _ => ((alphabet S).length:ℝ)*(spinPrecision C D.k:ℝ)/(S.ρ 1:ℝ)+
      (alphabet S).length/(2:ℝ)^spinBits S D.k) ha
    (fun i => spinWordLaw_tv S C (D.fields z i) D.k hC D.fuel hfSpin)
  have hkernel : kernelK S (D.sCap:ℝ) (castM D.L) (castV D.h) (castV z) =
      FiniteRetry.trial (FiniteKernelTV.productLaw q) b := by
    funext x
    have hg := SpinKernel.potential_gap S (D.sCap:ℝ) (castM D.L) (castV D.h) (castV z)
    simp_rw [← D.fields_cast z] at hg
    cases x <;> simp only [kernelK, hg, FiniteRetry.trial, b, FiniteKernelTV.productLaw,
      condP, q, ← D.fields_cast z]
  rw [kernelWordLaw_eq S C hC D z hfSpin hnil, hkernel]
  change tvDist (FiniteRetry.trial (FiniteKernelTV.productLaw p) a)
    (FiniteRetry.trial (FiniteKernelTV.productLaw q) b) ≤ _
  have hsume : (∑ _ : Fin N, (((alphabet S).length:ℝ)*(spinPrecision C D.k:ℝ)/(S.ρ 1:ℝ)+
      (alphabet S).length/(2:ℝ)^spinBits S D.k)) =
      (N:ℝ)*(((alphabet S).length:ℝ)*(spinPrecision C D.k:ℝ)/(S.ρ 1:ℝ)+
        (alphabet S).length/(2:ℝ)^spinBits S D.k) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hsume] at htv
  simpa only [KernelPrecisionBudget.error,add_assoc] using htv

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
  have hactual : r = fun y =>
      FiniteDraw.mean (fun w : Fin T → Fin (N*gaussianNoiseBits D.k) → Bool =>
        kernelWordLaw S C D (finitePath (D.next S) (fun _ => 0) w) y) := funext hmean
  have hideal : (fun x => ∫ z, SpinKernel.pointKernel S (D.sCap:ℝ) (castM D.L) (castV D.h) z x
        ∂D.trajectoryLaw S T (fun _ => 0)) = fun y =>
      FiniteDraw.mean (fun w : Fin T → Fin (N*gaussianNoiseBits D.k) → Bool =>
        kernelK S (D.sCap:ℝ) (castM D.L) (castV D.h)
          (castV (finitePath (D.next S) (fun _ => 0) w)) y) := by
    funext y
    have hm := SpinKernel.pointKernel_coordinate_measurable S (D.sCap:ℝ) (castM D.L) (castV D.h) hCk hLip y
    rw [D.integral_trajectoryLaw S T (fun _ => 0) _ hm,
      ← D.word_expectation S T (fun _ => 0)
        (fun z => SpinKernel.pointKernel S (D.sCap:ℝ) (castM D.L) (castV D.h) z y)]
    simp only [FiniteDraw.mean, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] <;> rfl
  rw [hactual,hideal]
  exact FiniteDraw.tv_mean
    (fun w : Fin T → Fin (N*gaussianNoiseBits D.k) → Bool =>
      kernelWordLaw S C D (finitePath (D.next S) (fun _ => 0) w))
    (fun w : Fin T → Fin (N*gaussianNoiseBits D.k) → Bool =>
      kernelK S (D.sCap:ℝ) (castM D.L) (castV D.h) (castV (finitePath (D.next S) (fun _ => 0) w)))
    (fun w =>
    kernelWordLaw_tv S hS C hC D (finitePath (D.next S) (fun _ => 0) w)
      hs hfSpin hTake hfIntegral hnil)

end
end CritWinSpin.LocalTM2.Compiled

end



set_option autoImplicit false
set_option linter.all false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
noncomputable section
open Classical IsingLTL.BeliefProp MeasureTheory CritWinSpin
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled CritWinSpin.Implementation

theorem solution {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C : ℕ) (hC : 0<C)
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
  exact numeric_trajectory_tv S hS C hC D T hs hfSpin hTake hfIntegral hnil r hmean Ck hCk hLip

#print axioms solution
