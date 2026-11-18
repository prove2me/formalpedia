-- Prove2me | solution 1 for CritWinSpin.regularized_envelope_budget
-- status  : ACCEPTED   (prove)
-- author  : @Maxliu
-- created : 2026-11-17T18:12:53.727773+00:00
-- url     : https://prove2.me/submissions/c4159237-ba70-47a9-ab7f-72d205434c7c

import Definitions.Def_CritWinSpin_SamplerAnalyticData
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Mathlib

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

def weighted (μ : Measure Ω) (F : Ω → ℝ) : Measure Ω := μ.withDensity fun x => ENNReal.ofReal (F x)



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

theorem abs_deriv_phis_le_one (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t : ℝ) : |deriv (phis S s) t| ≤ 1 := by
  rw [(hasDerivAt_phis_direct S hS hs t).deriv]
  obtain ⟨a, _, ha_eq, _, _, hasOf⟩ := asOf_props_direct S hS hs
  rw [hasOf]
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  split_ifs with hle
  · rw [abs_div, abs_of_pos hs_pos, div_le_one hs_pos]
    have hψ_le1 : deriv (phi S) a ≤ 1 := (abs_le.mp (deriv_phi_bdd S a)).2
    have ha_le_s : a ≤ s := by nlinarith
    exact hle.trans ha_le_s
  · exact deriv_phi_bdd S t

theorem phis_sub_le (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t₁ t₂ : ℝ) : |phis S s t₁ - phis S s t₂| ≤ |t₁ - t₂| := by
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := phis S s) (C := 1)
    (fun x _ => (hasDerivAt_phis_direct S hS hs x).differentiableAt)
    (fun x _ => by simpa [Real.norm_eq_abs] using abs_deriv_phis_le_one S hS hs x)
    (Set.mem_univ t₂) (Set.mem_univ t₁)
  simpa [Real.norm_eq_abs, one_mul] using h









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

theorem phis_taylor_bounds (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t₀ u : ℝ) :
    0 ≤ phis S s (t₀ + u) - phis S s t₀ - u * deriv (phis S s) t₀ ∧
      phis S s (t₀ + u) - phis S s t₀ - u * deriv (phis S s) t₀ ≤ u ^ 2 / (2 * s) ∧
      phis S s (t₀ + u) - phis S s t₀ - u * deriv (phis S s) t₀ ≤ 2 * |u| := by
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  have h2u : phis S s (t₀ + u) - phis S s t₀ - u * deriv (phis S s) t₀ ≤ 2 * |u| := by
    have h1 := phis_sub_le S hS hs (t₀ + u) t₀
    rw [show (t₀ + u) - t₀ = u by ring] at h1
    have h2 : |u * deriv (phis S s) t₀| ≤ |u| := by
      rw [abs_mul]
      calc |u| * |deriv (phis S s) t₀| ≤ |u| * 1 := by
            gcongr; exact abs_deriv_phis_le_one S hS hs t₀
        _ = |u| := mul_one _
    linarith [le_abs_self (phis S s (t₀ + u) - phis S s t₀),
      neg_le_abs (u * deriv (phis S s) t₀)]
  let F : ℝ → ℝ := fun r => phis S s (t₀ + r) - r * deriv (phis S s) t₀
  let G : ℝ → ℝ := fun r => F r - r ^ 2 / (2 * s)
  have hF_deriv : ∀ r, HasDerivAt F (deriv (phis S s) (t₀ + r) - deriv (phis S s) t₀) r :=
    fun r => by
      have hc0 := hasDerivAt_phis_direct S hS hs (t₀ + r)
      rw [← hc0.deriv] at hc0
      have hc := hc0.comp r ((hasDerivAt_id' r).const_add t₀)
      have hl : HasDerivAt (fun x : ℝ => x * deriv (phis S s) t₀) (deriv (phis S s) t₀) r := by
        simpa using (hasDerivAt_id' r).mul_const (deriv (phis S s) t₀)
      exact (hc.sub hl).congr_deriv (by ring)
  have hG_deriv : ∀ r,
      HasDerivAt G (deriv (phis S s) (t₀ + r) - deriv (phis S s) t₀ - r / s) r := fun r => by
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * s)) (r / s) r := by
      have h := ((hasDerivAt_id' r).pow 2).div_const (2 * s)
      rw [show (↑(2 : ℕ) * r ^ (2 - 1) * 1) / (2 * s) = r / s by
        calc ((↑(2 : ℕ) : ℝ) * r ^ (2 - 1) * 1) / (2 * s) = (2 * r) / (2 * s) := by norm_num
          _ = r / s := mul_div_mul_left r s (by norm_num)] at h
      exact h
    exact (hF_deriv r).sub hsq
  have hF0 : F 0 = phis S s t₀ := by simp [F]
  have hG0 : G 0 = phis S s t₀ := by simp [G, F]
  have hF_cont : Continuous F :=
    ((phis_continuous S s).comp (continuous_const.add continuous_id)).sub
      (continuous_id.mul continuous_const)
  have hG_cont : Continuous G :=
    hF_cont.sub ((continuous_pow 2).div_const _)
  have hB : 0 ≤ F u - F 0 ∧ F u - F 0 ≤ u ^ 2 / (2 * s) := by
    rcases le_or_gt 0 u with hu0 | hu0
    · have hF_mono : MonotoneOn F (Set.Icc 0 u) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u) hF_cont.continuousOn
          (fun r _ => (hF_deriv r).differentiableAt.differentiableWithinAt) fun r hr => ?_
        have hr' := interior_subset hr
        rw [(hF_deriv r).deriv]
        exact (deriv_phis_mono_and_lip S hS hs (by linarith [hr'.1] : t₀ ≤ t₀ + r)).1
      have hG_anti : AntitoneOn G (Set.Icc 0 u) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc 0 u) hG_cont.continuousOn
          (fun r _ => (hG_deriv r).differentiableAt.differentiableWithinAt) fun r hr => ?_
        have hr' := interior_subset hr
        rw [(hG_deriv r).deriv]
        have hstep := (deriv_phis_mono_and_lip S hS hs
          (by linarith [hr'.1] : t₀ ≤ t₀ + r)).2
        rw [show (1 / s) * (t₀ + r - t₀) = r / s by ring] at hstep
        linarith
      have h1 := hF_mono ⟨le_rfl, hu0⟩ ⟨hu0, le_rfl⟩ hu0
      have h2 := hG_anti ⟨le_rfl, hu0⟩ ⟨hu0, le_rfl⟩ hu0
      dsimp [G] at h2
      norm_num at h2
      exact ⟨by linarith, by linarith⟩
    · have hF_anti : AntitoneOn F (Set.Icc u 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc u 0) hF_cont.continuousOn
          (fun r _ => (hF_deriv r).differentiableAt.differentiableWithinAt) fun r hr => ?_
        have hr' := interior_subset hr
        rw [(hF_deriv r).deriv]
        have hstep := (deriv_phis_mono_and_lip S hS hs
          (by linarith [hr'.2] : t₀ + r ≤ t₀)).1
        linarith
      have hG_mono : MonotoneOn G (Set.Icc u 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc u 0) hG_cont.continuousOn
          (fun r _ => (hG_deriv r).differentiableAt.differentiableWithinAt) fun r hr => ?_
        have hr' := interior_subset hr
        rw [(hG_deriv r).deriv]
        have hstep := (deriv_phis_mono_and_lip S hS hs
          (by linarith [hr'.2] : t₀ + r ≤ t₀)).2
        rw [show (1 / s) * (t₀ - (t₀ + r)) = -(r / s) by ring] at hstep
        linarith
      have h1 := hF_anti ⟨le_rfl, hu0.le⟩ ⟨hu0.le, le_rfl⟩ hu0.le
      have h2 := hG_mono ⟨le_rfl, hu0.le⟩ ⟨hu0.le, le_rfl⟩ hu0.le
      dsimp [G] at h2
      norm_num at h2
      exact ⟨by linarith, by linarith⟩
  dsimp [F] at hB
  rw [add_zero, zero_mul, sub_zero] at hB
  exact ⟨by linarith [hB.1], by linarith [hB.2], h2u⟩

end SpinAndPhi

section LinearAlgebraAndHessian

theorem normSq_nonneg {N : ℕ} (v : Fin N → ℝ) : 0 ≤ normSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _







theorem normSq_transpose_mulVec_le {N : ℕ} {s : ℝ}
    {L : Matrix (Fin N) (Fin N) ℝ}
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (u : Fin N → ℝ) : normSq (L.transpose.mulVec u) ≤ s * normSq u := by
  have h0 := hPSD.dotProduct_mulVec_nonneg u
  have h1 : dotProduct u (Matrix.mulVec (s • (1 : Matrix (Fin N) (Fin N) ℝ)) u) = s * normSq u := by
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      normSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have h2 : dotProduct u (Matrix.mulVec (L * L.transpose) u) = normSq (L.transpose.mulVec u) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    unfold normSq dotProduct
    refine Finset.sum_congr rfl fun i _ => by ring
  change 0 ≤ dotProduct u (Matrix.mulVec (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose) u) at h0
  rw [Matrix.sub_mulVec, dotProduct_sub, h1, h2] at h0
  linarith

theorem normSq_mulVec_le {N : ℕ} {s : ℝ} (hs_nn : 0 ≤ s)
    {L : Matrix (Fin N) (Fin N) ℝ}
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (v : Fin N → ℝ) : normSq (L.mulVec v) ≤ s * normSq v := by
  let w := L.mulVec v
  have hw_nn : 0 ≤ normSq w := normSq_nonneg w
  rcases eq_or_lt_of_le hw_nn with hw0 | hwpos
  · rw [← hw0]
    exact mul_nonneg hs_nn (normSq_nonneg v)
  · have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N)) v (L.transpose.mulVec w)
    have hdot : ∑ i, v i * (L.transpose.mulVec w) i = normSq w := by
      change dotProduct v (L.transpose.mulVec w) = normSq w
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      unfold normSq dotProduct w
      refine Finset.sum_congr rfl fun i _ => by ring
    have hlt_w := normSq_transpose_mulVec_le hPSD w
    change (∑ i, v i * L.transpose.mulVec w i) ^ 2 ≤ normSq v * normSq (L.transpose.mulVec w) at hcs
    rw [hdot] at hcs
    have hle : normSq w ^ 2 ≤ normSq v * (s * normSq w) :=
      hcs.trans (mul_le_mul_of_nonneg_left hlt_w (normSq_nonneg v))
    have hsub : (s * normSq v - normSq w) * normSq w ≥ 0 := by nlinarith
    exact le_of_sub_nonneg (nonneg_of_mul_nonneg_left hsub hwpos)















end LinearAlgebraAndHessian

end CritWinSpin.Implementation.EnvelopeAnalysis

end

section

set_option autoImplicit false
open scoped RealInnerProductSpace
noncomputable section

namespace CritWinSpin.Implementation.SmoothGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gradient_descent_bound {U : E → ℝ} {g : E → E}
    (hlo : ∀ x y, 0 ≤ U y - U x - (inner ℝ (y - x) (g x)))
    (hhi : ∀ x y, U y - U x - (inner ℝ (y - x) (g x)) ≤ ‖y - x‖ ^ 2) (x y : E) :
    ‖g x - g y‖ ^ 2 / 4 ≤ U x - U y - (inner ℝ (x - y) (g y)) := by
  let v := g x - g y
  let z := x - (1 / 2 : ℝ) • v
  have h₁ := hlo y z
  have h₂ := hhi x z
  have hzx : z - x = -(1 / 2 : ℝ) • v := by dsimp [z]; module
  have hzy : z - y = (x - y) - (1 / 2 : ℝ) • v := by dsimp [z]; abel
  rw [hzx, inner_smul_left, norm_smul, Real.norm_eq_abs] at h₂
  rw [hzy, inner_sub_left, real_inner_smul_left] at h₁
  have he : (inner ℝ (v) (g x)) - (inner ℝ (v) (g y)) = ‖v‖ ^ 2 := by
    rw [← inner_sub_right]
    exact real_inner_self_eq_norm_sq v
  norm_num at h₂
  nlinarith

theorem gradient_lipschitz {U : E → ℝ} {g : E → E}
    (hlo : ∀ x y, 0 ≤ U y - U x - (inner ℝ (y - x) (g x)))
    (hhi : ∀ x y, U y - U x - (inner ℝ (y - x) (g x)) ≤ ‖y - x‖ ^ 2) (x y : E) :
    ‖g x - g y‖ ≤ 2 * ‖x - y‖ := by
  have hd := gradient_descent_bound hlo hhi x y
  have hh := hhi y x
  have hs : ‖g x - g y‖ ^ 2 ≤ (2 * ‖x - y‖) ^ 2 := by nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hs

theorem gradient_strong_monotone {U : E → ℝ} {g : E → E} {a : ℝ}
    (hlo : ∀ x y, (a / 2) * ‖y - x‖ ^ 2 ≤ U y - U x - (inner ℝ (y - x) (g x)))
    (x y : E) : a * ‖x - y‖ ^ 2 ≤ (inner ℝ (x - y) (g x - g y)) := by
  have h₁ := hlo x y
  have h₂ := hlo y x
  rw [show y - x = -(x - y) by abel, norm_neg, inner_neg_left] at h₁
  rw [inner_sub_right]
  linarith

theorem absolute_taylor {U : E → ℝ} {g : E → E}
    (hlo : ∀ x y, 0 ≤ U y - U x - (inner ℝ (y - x) (g x)))
    (hhi : ∀ x y, U y - U x - (inner ℝ (y - x) (g x)) ≤ ‖y - x‖ ^ 2) (x y : E) :
    |U y - U x - (inner ℝ (y - x) (g x))| ≤ ‖y - x‖ ^ 2 := by
  rw [abs_of_nonneg (hlo x y)]
  exact hhi x y

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



theorem increment_identity {N : ℕ} (S : SpinLaw) (s a : ℝ)
    (L : Matrix (Fin N) (Fin N) ℝ) (h z v : Fin N → ℝ) :
    Ualpha S s a L h (z + v) - Ualpha S s a L h z - dotProduct v (grad S s a L h z) =
      ((1 + a) / 2) * normSq v -
        ∑ i, (phis S s ((L.mulVec z i + h i) + L.mulVec v i) -
          phis S s (L.mulVec z i + h i) - L.mulVec v i * deriv (phis S s) (L.mulVec z i + h i)) := by
  have hg : dotProduct v (grad S s a L h z) =
      (1 + a) * (∑ j, z j * v j) -
        ∑ i, L.mulVec v i * deriv (phis S s) (L.mulVec z i + h i) := by
    unfold grad
    rw [dotProduct_sub, dotProduct_smul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    simp only [smul_eq_mul, dotProduct]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hns : normSq (z + v) = normSq z + 2 * (∑ j, z j * v j) + normSq v := by
    unfold normSq
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrem : (∑ i, (phis S s ((L.mulVec z i + h i) + L.mulVec v i) -
      phis S s (L.mulVec z i + h i) - L.mulVec v i * deriv (phis S s) (L.mulVec z i + h i))) =
      (∑ i, phis S s (L.mulVec z i + L.mulVec v i + h i)) -
        (∑ i, phis S s (L.mulVec z i + h i)) -
        ∑ i, L.mulVec v i * deriv (phis S s) (L.mulVec z i + h i) := by
    simp only [Finset.sum_sub_distrib]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  rw [hg, hrem]
  unfold Ualpha Wpot
  rw [hns, Matrix.mulVec_add]
  simp only [Pi.add_apply]
  ring

theorem taylor_bounds {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s a : ℝ} (hs : tau S < s)
    (L : Matrix (Fin N) (Fin N) ℝ) (h z v : Fin N → ℝ)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef) :
    (a / 2) * normSq v ≤
        Ualpha S s a L h (z + v) - Ualpha S s a L h z - dotProduct v (grad S s a L h z) ∧
      Ualpha S s a L h (z + v) - Ualpha S s a L h z - dotProduct v (grad S s a L h z) ≤
        ((1 + a) / 2) * normSq v := by
  have hspos := (tau_pos S).trans hs
  let R : Fin N → ℝ := fun i => phis S s ((L.mulVec z i + h i) + L.mulVec v i) -
    phis S s (L.mulVec z i + h i) - L.mulVec v i * deriv (phis S s) (L.mulVec z i + h i)
  have hR : ∀ i, 0 ≤ R i ∧ R i ≤ L.mulVec v i ^ 2 / (2 * s) := fun i =>
    ⟨(phis_taylor_bounds S hS hs _ _).1, (phis_taylor_bounds S hS hs _ _).2.1⟩
  have hnn : 0 ≤ ∑ i, R i := Finset.sum_nonneg fun i _ => (hR i).1
  have hbound : (∑ i, R i) ≤ (1 / 2) * normSq v := by
    calc
      _ ≤ ∑ i, L.mulVec v i ^ 2 / (2 * s) := Finset.sum_le_sum fun i _ => (hR i).2
      _ = normSq (L.mulVec v) / (2 * s) := by rw [← Finset.sum_div]; rfl
      _ ≤ (s * normSq v) / (2 * s) := by
        gcongr
        exact normSq_mulVec_le hspos.le hPSD v
      _ = (1 / 2) * normSq v := by field_simp [hspos.ne']
  rw [increment_identity]
  change (a / 2) * normSq v ≤ ((1 + a) / 2) * normSq v - ∑ i, R i ∧
    ((1 + a) / 2) * normSq v - (∑ i, R i) ≤ ((1 + a) / 2) * normSq v
  constructor <;> linarith







theorem normSq_coe {N : ℕ} (z : Point N) : normSq (fun i => z i) = ‖z‖ ^ 2 := by
  exact (EuclideanSpace.real_norm_sq_eq z).symm

theorem inner_coe {N : ℕ} (z v : Point N) :
    inner ℝ z v = dotProduct (fun i => z i) (fun i => v i) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem euclidean_taylor {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s a : ℝ} (hs : tau S < s)
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (x y : Point N) :
    (a / 2) * ‖y - x‖ ^ 2 ≤ potential S s a L h y - potential S s a L h x -
        inner ℝ (y - x) (gradient S s a L h x) ∧
      potential S s a L h y - potential S s a L h x - inner ℝ (y - x) (gradient S s a L h x) ≤
        ((1 + a) / 2) * ‖y - x‖ ^ 2 := by
  have ht := taylor_bounds S hS (a := a) hs L h (fun i => x i) (fun i => y i - x i) hPSD
  have he : ((fun i => x i) + fun i => y i - x i) = fun i => y i := by funext i; simp
  rw [he] at ht
  rw [inner_coe]
  change (a / 2) * ‖y - x‖ ^ 2 ≤ Ualpha S s a L h (fun i => y i) -
      Ualpha S s a L h (fun i => x i) - dotProduct (fun i => y i - x i) (grad S s a L h (fun i => x i)) ∧
    Ualpha S s a L h (fun i => y i) - Ualpha S s a L h (fun i => x i) -
      dotProduct (fun i => y i - x i) (grad S s a L h (fun i => x i)) ≤ ((1 + a) / 2) * ‖y - x‖ ^ 2
  have hn : normSq (fun i => y i - x i) = ‖y - x‖ ^ 2 := by
    simpa only [PiLp.sub_apply] using normSq_coe (y - x)
  rw [hn] at ht
  exact ht

theorem regular_geometry {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s a : ℝ} (hs : tau S < s)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef) :
    (∀ x y : Point N, a * ‖x - y‖ ^ 2 ≤
      inner ℝ (x - y) (gradient S s a L h x - gradient S s a L h y)) ∧
    (∀ x y : Point N, ‖gradient S s a L h x - gradient S s a L h y‖ ≤ 2 * ‖x - y‖) ∧
    (∀ x y : Point N, |potential S s a L h y - potential S s a L h x -
      inner ℝ (y - x) (gradient S s a L h x)| ≤ ‖y - x‖ ^ 2) := by
  have ht := euclidean_taylor S hS (a := a) hs L h hPSD
  have hlo : ∀ x y : Point N, 0 ≤ potential S s a L h y - potential S s a L h x -
      inner ℝ (y - x) (gradient S s a L h x) := fun x y =>
    (mul_nonneg (div_nonneg ha (by norm_num)) (sq_nonneg _)).trans (ht x y).1
  have hhi : ∀ x y : Point N, potential S s a L h y - potential S s a L h x -
      inner ℝ (y - x) (gradient S s a L h x) ≤ ‖y - x‖ ^ 2 := by
    intro x y
    exact (ht x y).2.trans (by nlinarith [sq_nonneg ‖y - x‖])
  exact ⟨SmoothGeometry.gradient_strong_monotone (fun x y => (ht x y).1),
    SmoothGeometry.gradient_lipschitz hlo hhi, SmoothGeometry.absolute_taylor hlo hhi⟩

theorem gradient_zero_bound {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s a : ℝ} (hs : tau S < s)
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef) :
    ‖gradient S s a L h 0‖ ^ 2 ≤ s * (N : ℝ) := by
  let u : Fin N → ℝ := fun i => deriv (phis S s) (h i)
  have hu : normSq u ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hb := abs_deriv_phis_le_one S hS hs (h i)
        change u i ^ 2 ≤ 1
        dsimp [u]
        simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 hb
      _ = _ := by simp
  have hb := normSq_transpose_mulVec_le hPSD u
  have hspos := (tau_pos S).trans hs
  have he : normSq (fun i => gradient S s a L h 0 i) = normSq (L.transpose.mulVec u) := by
    unfold normSq
    apply Finset.sum_congr rfl
    intro i _
    simp only [gradient, grad, WithLp.ofLp_toLp]
    change (((1 + a) * 0 - L.transpose.mulVec (fun j => deriv (phis S s) (L.mulVec 0 j + h j)) i) ^ 2) =
      L.transpose.mulVec u i ^ 2
    simp [Matrix.mulVec_zero, u]
  rw [← normSq_coe, he]
  exact hb.trans (mul_le_mul_of_nonneg_left hu hspos.le)

theorem gradient_growth {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s a : ℝ} (hs : tau S < s)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef) (z : Point N) :
    ‖gradient S s a L h z‖ ≤ 2 * ‖z‖ + Real.sqrt (s * (N : ℝ)) := by
  have hl := (regular_geometry S hS hs ha ha1 L h hPSD).2.1 z 0
  rw [sub_zero] at hl
  have hz := gradient_zero_bound S hS (a := a) hs L h hPSD
  have hz' := Real.le_sqrt_of_sq_le hz
  have hn := norm_add_le (gradient S s a L h z - gradient S s a L h 0) (gradient S s a L h 0)
  rw [sub_add_cancel] at hn
  linarith

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

theorem square_exp_neg (u : ℝ) (hu : 0 ≤ u) : u ^ 2 * Real.exp (-u) ≤ 4 := by
  have he : u / 2 ≤ Real.exp (u / 2) := by linarith [Real.add_one_le_exp (u / 2)]
  have hs : (u / 2) ^ 2 ≤ (Real.exp (u / 2)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (Real.exp_pos _).le).2 he
  have hexp : (Real.exp (u / 2)) ^ 2 = Real.exp u := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hs
  have hsq : u ^ 2 ≤ 4 * Real.exp u := by nlinarith
  calc
    u ^ 2 * Real.exp (-u) ≤ (4 * Real.exp u) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = 4 := by rw [mul_assoc, ← Real.exp_add]; norm_num

theorem cube_damping (a r : ℝ) (ha : 0 < a) (hr : 0 ≤ r) :
    r ^ 3 * Real.exp (-(a * r / 2)) ≤ (16 / a ^ 2) * r := by
  have hs := square_exp_neg (a * r / 2) (by positivity)
  calc
    r ^ 3 * Real.exp (-(a * r / 2)) =
        (4 * r / a ^ 2) * ((a * r / 2) ^ 2 * Real.exp (-(a * r / 2))) := by
      field_simp
      <;> ring
    _ ≤ (4 * r / a ^ 2) * 4 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (16 / a ^ 2) * r := by ring

noncomputable def damped {Ω : Type} (f R : Ω → ℝ) (a : ℝ) (x : Ω) : ℝ :=
  f x * Real.exp (-(a * R x / 2))

theorem damped_nonneg {Ω : Type} (f R : Ω → ℝ) (a : ℝ)
    (hf : ∀ x, 0 ≤ f x) (x : Ω) : 0 ≤ damped f R a x := by
  exact mul_nonneg (hf x) (Real.exp_pos _).le

theorem damped_le {Ω : Type} (f R : Ω → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hf : ∀ x, 0 ≤ f x) (hR : ∀ x, 0 ≤ R x) (x : Ω) :
    damped f R a x ≤ f x := by
  have he : Real.exp (-(a * R x / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (mul_nonneg ha (hR x)) (by norm_num)))
  exact (mul_le_mul_of_nonneg_left he (hf x)).trans_eq (mul_one _)

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f R : Ω → ℝ)

theorem damped_measurable (a : ℝ) (hf : Measurable f) (hR : Measurable R) :
    Measurable (damped f R a) := by
  exact hf.mul (((hR.const_mul a).div_const 2).neg.exp)

theorem damped_integrable (a : ℝ) (ha : 0 ≤ a)
    (hf : ∀ x, 0 ≤ f x) (hR : ∀ x, 0 ≤ R x)
    (hmf : Measurable f) (hmR : Measurable R) (hif : Integrable f μ) :
    Integrable (damped f R a) μ := by
  refine hif.mono' (damped_measurable f R a hmf hmR).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (damped_nonneg f R a hf x)]
  exact damped_le f R a ha hf hR x

theorem mass_lower (a : ℝ) (ha : 0 ≤ a)
    (hf : ∀ x, 0 ≤ f x) (hR : ∀ x, 0 ≤ R x)
    (hmf : Measurable f) (hmR : Measurable R)
    (hif : Integrable f μ) (hiR : Integrable (fun x => R x * f x) μ)
    (hf1 : ∫ x, f x ∂μ = 1) :
    1 - (a / 2) * (∫ x, R x * f x ∂μ) ≤ ∫ x, damped f R a x ∂μ := by
  have hd := damped_integrable μ f R a ha hf hR hmf hmR hif
  have hc := hiR.const_mul (a / 2)
  have hp : ∀ x, f x - (a / 2) * (R x * f x) ≤ damped f R a x := by
    intro x
    have he : 1 - a * R x / 2 ≤ Real.exp (-(a * R x / 2)) := by
      linarith [Real.add_one_le_exp (-(a * R x / 2))]
    calc
      f x - (a / 2) * (R x * f x) = f x * (1 - a * R x / 2) := by ring
      _ ≤ damped f R a x := mul_le_mul_of_nonneg_left he (hf x)
  have hh := integral_mono (hif.sub hc) hd hp
  change (∫ x, f x - (a / 2) * (R x * f x) ∂μ) ≤ ∫ x, damped f R a x ∂μ at hh
  rw [integral_sub hif hc, integral_const_mul, hf1] at hh
  exact hh

theorem cube_integrable_and_bound (a : ℝ) (ha : 0 < a)
    (hf : ∀ x, 0 ≤ f x) (hR : ∀ x, 0 ≤ R x)
    (hmf : Measurable f) (hmR : Measurable R)
    (hiR : Integrable (fun x => R x * f x) μ) :
    Integrable (fun x => (R x) ^ 3 * damped f R a x) μ ∧
      (∫ x, (R x) ^ 3 * damped f R a x ∂μ) ≤
        (16 / a ^ 2) * (∫ x, R x * f x ∂μ) := by
  have hm := (hmR.pow_const 3).mul (damped_measurable f R a hmf hmR)
  have hb : ∀ x, (R x) ^ 3 * damped f R a x ≤ (16 / a ^ 2) * (R x * f x) := by
    intro x
    calc
      (R x) ^ 3 * damped f R a x =
          ((R x) ^ 3 * Real.exp (-(a * R x / 2))) * f x := by unfold damped; ring
      _ ≤ ((16 / a ^ 2) * R x) * f x :=
        mul_le_mul_of_nonneg_right (cube_damping a (R x) ha (hR x)) (hf x)
      _ = (16 / a ^ 2) * (R x * f x) := by ring
  have hc := hiR.const_mul (16 / a ^ 2)
  have hi : Integrable (fun x => (R x) ^ 3 * damped f R a x) μ := by
    refine hc.mono' hm.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (hR x) 3)
      (damped_nonneg f R a hf x))]
    exact hb x
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hc hb
  rw [integral_const_mul] at hh
  exact hh

theorem normalized_cube_bound (a : ℝ) (ha : 0 < a)
    (hf : ∀ x, 0 ≤ f x) (hR : ∀ x, 0 ≤ R x)
    (hmf : Measurable f) (hmR : Measurable R)
    (hif : Integrable f μ) (hiR : Integrable (fun x => R x * f x) μ)
    (hf1 : ∫ x, f x ∂μ = 1)
    (hsmall : a * (∫ x, R x * f x ∂μ) ≤ 1) :
    (1 / 2 : ℝ) ≤ (∫ x, damped f R a x ∂μ) ∧
      (∫ x, (R x) ^ 3 * damped f R a x ∂μ) / (∫ x, damped f R a x ∂μ) ≤
        (32 / a ^ 2) * (∫ x, R x * f x ∂μ) := by
  have hz := mass_lower μ f R a ha.le hf hR hmf hmR hif hiR hf1
  have hzhalf : (1 / 2 : ℝ) ≤ ∫ x, damped f R a x ∂μ := by nlinarith
  refine ⟨hzhalf, ?_⟩
  have hzpos : 0 < ∫ x, damped f R a x ∂μ := by linarith
  have hm0 : 0 ≤ ∫ x, R x * f x ∂μ := integral_nonneg fun x => mul_nonneg (hR x) (hf x)
  have hc := (cube_integrable_and_bound μ f R a ha hf hR hmf hmR hiR).2
  rw [div_le_iff₀ hzpos]
  have he := mul_le_mul_of_nonneg_right hzhalf
    (show 0 ≤ (32 / a ^ 2) * (∫ x, R x * f x ∂μ) by positivity)
  calc
    _ ≤ (16 / a ^ 2) * (∫ x, R x * f x ∂μ) := hc
    _ = (1 / 2) * ((32 / a ^ 2) * (∫ x, R x * f x ∂μ)) := by ring
    _ ≤ (∫ x, damped f R a x ∂μ) * ((32 / a ^ 2) * (∫ x, R x * f x ∂μ)) := he
    _ = _ := by ring

end CritWinSpin.Implementation.Regularization

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.RegularizedGibbsMoments

open DensityAnalysis

theorem sixth_moment {d : ℕ} {W U : Point d → ℝ} {a M : ℝ}
    (ha : 0 < a) (hW : Continuous W) (hU : Continuous U)
    (hUeq : ∀ x, U x = W x + (a / 2) * ‖x‖ ^ 2)
    (hiW : Integrable (fun x => Real.exp (-W x)))
    (hiW2 : Integrable (fun x => ‖x‖ ^ 2 * Real.exp (-W x)))
    (hiU : Integrable (fun x => Real.exp (-U x)))
    (hMom : (∫ x, ‖x‖ ^ 2 ∂DensityAnalysis.gibbs W) ≤ M) (hsmall : a * M ≤ 1) :
    Integrable (fun x => ‖x‖ ^ 6) (DensityAnalysis.gibbs U) ∧
      (∫ x, ‖x‖ ^ 6 ∂DensityAnalysis.gibbs U) ≤ (32 / a ^ 2) * M := by
  let Z : ℝ := ∫ x, Real.exp (-W x)
  have hZ : 0 < Z := integral_exp_pos hiW
  let f : Point d → ℝ := fun x => Real.exp (-W x) / Z
  let R : Point d → ℝ := fun x => ‖x‖ ^ 2
  have hif : Integrable f := hiW.div_const Z
  have hmF : Measurable f := by dsimp [f]; fun_prop
  have hmR : Measurable R := by dsimp [R]; fun_prop
  have hf0 : ∀ x, 0 ≤ f x := fun x => div_nonneg (Real.exp_pos _).le hZ.le
  have hR0 : ∀ x, 0 ≤ R x := fun x => sq_nonneg _
  have hiRf : Integrable (fun x => R x * f x) := by
    convert hiW2.div_const Z using 1
    funext x
    dsimp [R, f]
    ring
  have hf1 : ∫ x, f x = 1 := by
    dsimp [f]
    rw [integral_div]
    exact div_self hZ.ne'
  have hMf : (∫ x, R x * f x) ≤ M := by
    rw [integral_gibbs hW hiW] at hMom
    convert hMom using 1
    dsimp [R, f]
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hsmall' : a * (∫ x, R x * f x) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hMf ha.le).trans hsmall
  have hb := Regularization.normalized_cube_bound volume f R a ha hf0 hR0 hmF hmR hif hiRf hf1 hsmall'
  have hiC := (Regularization.cube_integrable_and_bound volume f R a ha hf0 hR0 hmF hmR hiRf).1
  have hd : ∀ x, Regularization.damped f R a x = Real.exp (-U x) / Z := by
    intro x
    rw [hUeq]
    dsimp [Regularization.damped, f, R]
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  have hnum : (fun x : Point d => R x ^ 3 * Regularization.damped f R a x) =
      fun x => (Real.exp (-U x) * ‖x‖ ^ 6) / Z := by
    funext x
    rw [hd]
    dsimp [R]
    rw [← pow_mul]
    ring
  have hi6 : Integrable (fun x => Real.exp (-U x) * ‖x‖ ^ 6) := by
    rw [hnum] at hiC
    convert hiC.mul_const Z using 1
    funext x
    field_simp [hZ.ne']
  have heRatio :
      (∫ x, R x ^ 3 * Regularization.damped f R a x) /
          (∫ x, Regularization.damped f R a x) = ∫ x, ‖x‖ ^ 6 ∂DensityAnalysis.gibbs U := by
    rw [hnum]
    simp_rw [hd]
    rw [integral_div, integral_div, integral_gibbs hU hiU]
    field_simp [hZ.ne']
  refine ⟨integrable_gibbs_of_weighted hU hiU hi6, ?_⟩
  rw [← heRatio]
  exact hb.2.trans (mul_le_mul_of_nonneg_left hMf (by positivity))

theorem sixth_growth_integrable_and_bound {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {g : E → E} (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B)
    (hGrowth : ∀ x, ‖g x‖ ≤ 2 * ‖x‖ + B)
    (hi6 : Integrable (fun x : E => ‖x‖ ^ 6) μ) :
    Integrable (fun x => ‖g x‖ ^ 6) μ ∧
      (∫ x, ‖g x‖ ^ 6 ∂μ) ≤ 2048 * (∫ x, ‖x‖ ^ 6 ∂μ) + 32 * B ^ 6 := by
  have hb : ∀ x : E, ‖g x‖ ^ 6 ≤ 2048 * ‖x‖ ^ 6 + 32 * B ^ 6 := by
    intro x
    have h₁ := pow_le_pow_left₀ (norm_nonneg _) (hGrowth x) 6
    have h₂ := add_pow_le (by positivity : 0 ≤ 2 * ‖x‖) hB 6
    norm_num at h₂
    nlinarith
  have hi : Integrable (fun x : E => 2048 * ‖x‖ ^ 6 + 32 * B ^ 6) μ :=
    (hi6.const_mul _).add (integrable_const _)
  have hig : Integrable (fun x : E => ‖g x‖ ^ 6) μ := by
    refine hi.mono' (hg.norm.pow 6).measurable.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb x
  refine ⟨hig, ?_⟩
  have hh := integral_mono hig hi hb
  rw [integral_add (hi6.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hh
  exact hh

theorem first_from_sixth {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (hi6 : Integrable (fun x : E => ‖x‖ ^ 6) μ) :
    Integrable (fun x : E => ‖x‖) μ ∧
      (∫ x : E, ‖x‖ ∂μ) ≤ 1 + ∫ x : E, ‖x‖ ^ 6 ∂μ := by
  have hb : ∀ x : E, ‖x‖ ≤ 1 + ‖x‖ ^ 6 := by
    intro x
    by_cases hx : ‖x‖ ≤ 1
    · linarith [pow_nonneg (norm_nonneg x) 6]
    · have hp : ‖x‖ ≤ ‖x‖ ^ 6 := by
        simpa only [pow_one] using pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hx)) (show 1 ≤ 6 by decide)
      linarith
  have hiB : Integrable (fun x : E => 1 + ‖x‖ ^ 6) μ := (integrable_const _).add hi6
  have hi : Integrable (fun x : E => ‖x‖) μ := by
    refine hiB.mono' continuous_norm.measurable.aestronglyMeasurable ?_
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_norm] using hb x
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hiB hb
  rw [integral_add (f := fun _ : E => (1 : ℝ)) (g := fun x => ‖x‖ ^ 6) (integrable_const _) hi6,
    integral_const, probReal_univ, one_smul] at hh
  exact hh

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

theorem sixth_moment {N : ℕ} (S : SpinLaw) {s a : ℝ}
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    {M : ℝ} (ha : 0 < a) (hsmall : a * M ≤ 1)
    (hiW : Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z)))
    (hiW2 : Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Wpot S s L h z)))
    (hiU : Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S s a L h z)))
    (hMom : (∫ z : Fin N → ℝ, normSq z * normDens (Wpot S s L h) z) ≤ M) :
    Integrable (fun z : EnvelopeGeometry.Point N => ‖z‖ ^ 6) (DensityAnalysis.gibbs (potential S s a L h)) ∧
      (∫ z : EnvelopeGeometry.Point N, ‖z‖ ^ 6 ∂DensityAnalysis.gibbs (potential S s a L h)) ≤ (32 / a ^ 2) * M := by
  let W : EnvelopeGeometry.Point N → ℝ := fun z => Wpot S s L h (fun i => z i)
  have hW : Continuous W := by
    have he : potential S s 0 L h = W := by
      funext z
      simp [potential, Ualpha, W]
    rw [← he]
    exact continuous_potential S s 0 L h
  have hiW' : Integrable (fun z : EnvelopeGeometry.Point N => Real.exp (-W z)) :=
    (PiVolumeTransfer.integrable_iff _).2 hiW
  have hiW2' : Integrable (fun z : EnvelopeGeometry.Point N => ‖z‖ ^ 2 * Real.exp (-W z)) := by
    have hh := (PiVolumeTransfer.integrable_iff _).2 hiW2
    simpa only [normSq_coe] using hh
  have hiU' : Integrable (fun z : EnvelopeGeometry.Point N => Real.exp (-potential S s a L h z)) :=
    (PiVolumeTransfer.integrable_iff _).2 hiU
  have hMom' : (∫ z : EnvelopeGeometry.Point N, ‖z‖ ^ 2 ∂DensityAnalysis.gibbs W) ≤ M := by
    have he := PiVolumeTransfer.gibbs_integral_eq (Wpot S s L h) normSq hW hiW
    simpa only [normSq_coe] using he.le.trans hMom
  have hEq : ∀ z : EnvelopeGeometry.Point N, potential S s a L h z = W z + (a / 2) * ‖z‖ ^ 2 := by
    intro z
    simp only [potential, Ualpha, normSq_coe, W]
  exact RegularizedGibbsMoments.sixth_moment ha hW (continuous_potential S s a L h)
    hEq hiW' hiW2' hiU' hMom' hsmall

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

theorem exists_certificate {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s a M : ℝ}
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hs : tau S < s) (ha : 0 < a) (ha1 : a ≤ 1)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (hsmall : a * M ≤ 1)
    (hiW : Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z)))
    (hiW2 : Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Wpot S s L h z)))
    (hiU : Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S s a L h z)))
    (hMom : (∫ z : Fin N → ℝ, normSq z * normDens (Wpot S s L h) z) ≤ M) :
    ∃ cert : Certificate N a,
      cert.U = potential S s a L h ∧ cert.g = gradient S s a L h ∧
      (∫ x, ‖x‖ ∂DensityAnalysis.gibbs cert.U) ≤ 1 + (32 / a ^ 2) * M ∧
      (∫ x, ‖cert.g x‖ ^ 6 ∂DensityAnalysis.gibbs cert.U) ≤
        (65536 / a ^ 2) * M + 32 * (s * (N : ℝ)) ^ 3 := by
  have hgeom := regular_geometry S hS hs ha.le ha1 L h hPSD
  have hgLip : LipschitzWith 2 (gradient S s a L h) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖gradient S s a L h x - gradient S s a L h y‖ ≤ 2 * ‖x - y‖
    exact hgeom.2.1 x y
  have hiU' : Integrable (fun z : DensityAnalysis.Point N => Real.exp (-potential S s a L h z)) :=
    (PiVolumeTransfer.integrable_iff _).2 hiU
  letI : IsProbabilityMeasure (DensityAnalysis.gibbs (potential S s a L h)) := gibbs_probability hiU'
  have h6 := EnvelopeMoments.sixth_moment S L h ha hsmall hiW hiW2 hiU hMom
  have hFirst := RegularizedGibbsMoments.first_from_sixth _ h6.1
  have hg6 := RegularizedGibbsMoments.sixth_growth_integrable_and_bound
    (DensityAnalysis.gibbs (potential S s a L h)) hgLip.continuous
    (Real.sqrt_nonneg (s * (N : ℝ))) (gradient_growth S hS hs ha.le ha1 L h hPSD) h6.1
  let cert : Certificate N a := {
    U := potential S s a L h
    g := gradient S s a L h
    continuous_U := continuous_potential S s a L h
    continuous_g := hgLip.continuous
    density_integrable := hiU'
    monotone := hgeom.1
    taylor := hgeom.2.2
    lipschitz := fun x y => (hgeom.2.1 x y).trans (by nlinarith only [norm_nonneg (x-y)])
    grad_integrable := hg6.1
    norm_integrable := hFirst.1 }
  refine ⟨cert, rfl, rfl, hFirst.2.trans (by linarith only [h6.2]), ?_⟩
  have hB : (Real.sqrt (s * (N : ℝ))) ^ 6 = (s * (N : ℝ)) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul,
      Real.sq_sqrt (mul_nonneg ((EnvelopeAnalysis.tau_pos S).trans hs).le (Nat.cast_nonneg N))]
  have hscaled := mul_le_mul_of_nonneg_left h6.2 (by norm_num : (0:ℝ) ≤ 2048)
  have ht : (∫ x, ‖gradient S s a L h x‖ ^ 6 ∂DensityAnalysis.gibbs (potential S s a L h)) ≤
      2048 * ((32 / a ^ 2) * M) + 32 * (Real.sqrt (s * (N : ℝ))) ^ 6 := by
    linarith only [hg6.2, hscaled]
  rw [hB] at ht
  change (∫ x, ‖gradient S s a L h x‖ ^ 6 ∂DensityAnalysis.gibbs (potential S s a L h)) ≤ _
  exact ht.trans_eq (by ring)

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
  let B := baseBudget C N t
  have hCp : 0 < C := by linarith only [hC]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbase : C * ((N : ℝ) + 1) ≤ B := by
    dsimp [B, baseBudget]
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ t + 1 by linarith only [ht])
      (show 0 ≤ C * ((N : ℝ) + 1) by positivity)
    simpa only [mul_one] using hh
  have hCB : C ≤ B := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ (N : ℝ) + 1 by linarith only [hN]) hCp.le
    rw [mul_one] at hh
    exact hh.trans hbase
  have hB : 131072 ≤ B := hC.trans hCB
  have hBp : 0 < B := by linarith only [hB]
  have hNB : (N : ℝ) ≤ B := by
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ C by linarith only [hC])
      (show 0 ≤ (N : ℝ) + 1 by positivity)
    rw [one_mul] at hh
    linarith only [hh, hbase]
  have hMB : M₀ * (N : ℝ) ≤ B := by
    have hh := mul_le_mul_of_nonneg_right (show M₀ ≤ C by nlinarith only [hMC, hM₀]) hN
    have hc : C * (N : ℝ) ≤ C * ((N : ℝ) + 1) := by nlinarith only [hCp]
    exact hh.trans (hc.trans hbase)
  have hspos := (EnvelopeAnalysis.tau_pos S).trans hs
  have hDB : s * (N : ℝ) ≤ B := by
    have hh := mul_le_mul_of_nonneg_right hsC hN
    have hc : C * (N : ℝ) ≤ C * ((N : ℝ) + 1) := by nlinarith only [hCp]
    exact hh.trans (hc.trans hbase)
  have hGB : GaussianMoments.sixthConstant * (N : ℝ) ^ 3 ≤ B ^ 4 := by
    have hh := mul_le_mul (hGC.trans hCB) (pow_le_pow_left₀ hN hNB 3)
      (pow_nonneg hN 3) hBp.le
    nlinarith only [hh]
  obtain ⟨hBR, hR, ha, ha1, haM, haR, hFirst, hGrad⟩ :=
    MomentBudget.bounds hB hMB (mul_nonneg hspos.le hN) hDB hGB
  obtain ⟨cert, hU, hg, hM1, hG6⟩ := EnvelopeCertificate.exists_certificate S hS L h
    hs ha ha1 hPSD haM hiW hiW2 hiU hMom
  have hKR : 2 * (Cₖ * Real.sqrt (N : ℝ)) ≤ B ^ 100 := by
    have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) + 1 := by
      have hh := Real.sqrt_le_sqrt (show (N : ℝ) ≤ ((N : ℝ) + 1) ^ 2 by nlinarith only [hN])
      rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)] at hh
    have hh := mul_le_mul hKC hsqrt (Real.sqrt_nonneg _) hCp.le
    have hh' : 2 * (Cₖ * Real.sqrt (N : ℝ)) ≤ C * ((N : ℝ) + 1) := by nlinarith only [hh]
    exact hh'.trans (hbase.trans hBR)
  have hReg : (1 / B) * M₀ * (N : ℝ) / 2 ≤ 1 / (4096 * (t + 1)) := by
    have hM : 2048 * M₀ * (N : ℝ) ≤ C * ((N : ℝ) + 1) := by
      have hh := mul_le_mul_of_nonneg_right hMC hN
      nlinarith only [hh, hCp]
    have hm := mul_le_mul_of_nonneg_right hM (show 0 ≤ t + 1 by positivity)
    apply (le_div_iff₀ (by positivity : 0 < 4096 * (t + 1))).2
    have he : ((1 / B) * M₀ * (N : ℝ) / 2) * (4096 * (t + 1)) =
        (2048 * M₀ * (N : ℝ) * (t + 1)) / B := by ring
    rw [he]
    apply (div_le_iff₀ hBp).2
    dsimp [B, baseBudget]
    nlinarith only [hm]
  have hnoise : 1 / (4 * B ^ 100) ≤ 1 / (4096 * (t + 1)) := by
    have htB : 1024 * (t + 1) ≤ B := by
      have hh := mul_le_mul_of_nonneg_right (show (1024 : ℝ) ≤ C by linarith only [hC])
        (show 0 ≤ t + 1 by positivity)
      have hn := mul_le_mul_of_nonneg_right (show 1 ≤ (N : ℝ) + 1 by linarith only [hN])
        (show 0 ≤ C * (t + 1) by positivity)
      dsimp [B, baseBudget]
      nlinarith only [hh, hn]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith only [htB, hBR])
  refine ⟨cert, hU, hg, ha, ha1, hR, haR, hM1.trans hFirst, ?_, hKR, ?_⟩
  · exact (add_le_add (add_le_add le_rfl hG6) le_rfl).trans (by
      simpa only [add_assoc] using hGrad)
  · have hh := add_le_add hnoise hReg
    have he : 1 / (4096 * (t + 1)) + 1 / (4096 * (t + 1)) = 1 / (2048 * (t + 1)) := by
      field_simp [show t + 1 ≠ 0 by positivity] <;> ring
    exact hh.trans_eq he

end CritWinSpin.Implementation.EnvelopeParameters
end

end



set_option autoImplicit false
set_option linter.all false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory CritWinSpin
open CritWinSpin.Implementation
open DensityAnalysis EnvelopeGeometry LangevinBudget

theorem solution {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s C M₀ Cₖ t : ℝ}
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hs : tau S < s) (hsC : s ≤ C) (ht : 0 ≤ t)
    (hC : 131072 ≤ C) (hM₀ : 0 ≤ M₀) (hMC : 2048 * M₀ ≤ C)
    (hCₖ : 0 ≤ Cₖ) (hKC : 2 * Cₖ ≤ C) (hGC : GaussianMoments.sixthConstant ≤ C)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (hiW : Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z)))
    (hiW2 : Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Wpot S s L h z)))
    (hiU : Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S s (1 / (C * ((N : ℝ) + 1) * (t + 1))) L h z)))
    (hMom : (∫ z : Fin N → ℝ, normSq z * normDens (Wpot S s L h) z) ≤ M₀ * (N : ℝ)) :
    let B := (C * ((N : ℝ) + 1) * (t + 1))
    ∃ cert : Certificate N (1 / B),
      cert.U = potential S s (1 / B) L h ∧ cert.g = gradient S s (1 / B) L h ∧
      0 < 1 / B ∧ 1 / B ≤ 1 ∧ 2 ≤ B ^ 100 ∧ 1 ≤ (1 / B) * B ^ 100 ∧
      (∫ x, ‖x‖ ∂DensityAnalysis.gibbs cert.U) ≤ B ^ 100 ∧
      2 + (∫ x, ‖cert.g x‖ ^ 6 ∂DensityAnalysis.gibbs cert.U) +
        GaussianMoments.sixthConstant * (N : ℝ) ^ 3 ≤ B ^ 100 ∧
      2 * (Cₖ * Real.sqrt (N : ℝ)) ≤ B ^ 100 ∧
      1 / (4 * B ^ 100) + (1 / B) * M₀ * (N : ℝ) / 2 ≤ 1 / (2048 * (t + 1)) := by
  simpa only [EnvelopeParameters.baseBudget] using
    (EnvelopeParameters.setup S hS L h hs hsC ht hC hM₀ hMC hCₖ hKC hGC hPSD
      hiW hiW2 hiU hMom)

#print axioms solution
