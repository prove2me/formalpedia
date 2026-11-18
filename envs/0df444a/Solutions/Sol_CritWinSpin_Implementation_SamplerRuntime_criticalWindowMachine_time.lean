-- Prove2me | solution 1 for CritWinSpin.Implementation.SamplerRuntime.criticalWindowMachine_time
-- status  : ACCEPTED   (prove)
-- author  : @Maxliu
-- created : 2026-11-17T18:25:04.325698+00:00
-- url     : https://prove2.me/submissions/f4ad6fc5-2d56-4a9b-9df7-f2966ff11678

import Mathlib
import Definitions.Def_CritWinSpin_SamplerMachine
import Theorems.Thm_CritWinSpin_lemma_4_2
import Theorems.Thm_CritWinSpin_sampler_smoothed_cap_budget

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

theorem phi_zero (S : SpinLaw) : phi S 0 = 0 := by
  unfold phi
  change Real.log (mgf S 0) = 0
  rw [mgf_zero, Real.log_one]

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

end CritWinSpin.Implementation.EnvelopeGeometry

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CritWinSpin.Implementation.PiVolumeTransfer

open DensityAnalysis

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

theorem ofFn_flatMap {α β : Type} {N : ℕ} (f : Fin N → α) (g : α → List β) :
    (List.ofFn f).flatMap g = (List.ofFn (fun i => g (f i))).flatten := by
  induction N with
  | zero => rfl
  | succ N ih => simp [List.ofFn_succ, ih]

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

end DyadicRounding

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
namespace FiniteTicket

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

theorem candidatePSD_complete {N : ℕ} (S : SpinLaw) (C j : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hC : 8 ≤ C)
    (hJ : (castM J).PosSemidef)
    (hu : (candidateLevel S C (List.replicate N (), j) : ℝ) ≤ 2 * tau S)
    (hShift : ((candidateLevel S C (List.replicate N (), j) : ℝ) •
      (1 : Matrix (Fin N) (Fin N) ℝ) - castM J).PosSemidef) :
    candidatePSD S C (encodedInput J, j) = true := by
  let u := candidateLevel S C (List.replicate N (), j)
  let A := shiftMatrix S J u
  let H : ℝ := fixedScale S
  have hH : 0 < H := by
    change (0 : ℝ) < (fixedScale S : ℝ)
    exact_mod_cast fixedScale_pos S
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hη : 0 < preTolerance C (List.replicate N ()) := by
    unfold preTolerance
    have hc : (0 : ℚ) < C := by exact_mod_cast hCpos
    positivity
  have hA : (castM A).PosSemidef := by
    rw [show A = shiftMatrix S J u from rfl, cast_shiftMatrix]
    exact hShift.smul (by positivity : 0 ≤ 1 / H)
  have hA1 : ((1 : Matrix (Fin N) (Fin N) ℝ) - castM A).PosSemidef := by
    have huH : 0 ≤ H - (u : ℝ) := by dsimp [H]; rw [fixedScale_cast]; linarith only [hu]
    have hh := (((Matrix.PosSemidef.one (n := Fin N) (R := ℝ)).smul huH).add hJ).smul
      (by positivity : 0 ≤ 1 / H)
    have he : (1 / H) • ((H - (u : ℝ)) • (1 : Matrix (Fin N) (Fin N) ℝ) + castM J) =
        1 - castM A := by
      rw [show A = shiftMatrix S J u from rfl, cast_shiftMatrix]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      change (1 / H) * ((H - (u : ℝ)) * (1 : Matrix (Fin N) (Fin N) ℝ) i j + castM J i j) =
        (1 : Matrix (Fin N) (Fin N) ℝ) i j - (1/H) * ((u : ℝ) * (1 : Matrix (Fin N) (Fin N) ℝ) i j - castM J i j)
      field_simp [hH.ne'] <;> ring
    rwa [he] at hh
  have hT : 8 ≤ (preTolerance C (List.replicate N ()) : ℝ) *
      (((polynomialFuel (C * C) 3 (List.replicate N ())).length : ℝ) + 2) := by
    rw [preTolerance_cast, polynomialFuel_length, List.length_replicate]
    push_cast
    have hp : 0 < ((N : ℝ) + 1) := by positivity
    have he : (1 / ((C : ℝ) * ((N : ℝ) + 1) ^ 3)) *
        ((C : ℝ) * C * ((N : ℝ) + 1) ^ 3 + 2) =
          (C : ℝ) + 2 / ((C : ℝ) * ((N : ℝ) + 1) ^ 3) := by
      field_simp [hCpos.ne', hp.ne'] <;> ring
    rw [he]
    have hc : (8 : ℝ) ≤ C := by exact_mod_cast hC
    have hd : 0 ≤ 2 / ((C : ℝ) * ((N : ℝ) + 1) ^ 3) := by positivity
    linarith only [hc, hd]
  have ht := approximatePSDTest_complete A hA hA1 _ hη
    (polynomialFuel (C*C) 3 (List.replicate N ())) hT
  simpa only [candidatePSD, encodedInput, normalizedShift_encoded] using ht

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

theorem last_level {N : ℕ} (S : SpinLaw) (C : ℕ) (hC : 0 < C) :
    (candidateLevel S C (List.replicate N (), C * (N+1)) : ℝ) = 2 * tau S := by
  rw [candidateLevel_cast]
  push_cast
  rw [div_self (show (C : ℝ) * ((N : ℝ)+1) ≠ 0 by positivity)]
  ring

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

theorem inside_false_supercritical {N : ℕ} (S : SpinLaw) (C : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hC : 8 ≤ C)
    (hJ : (castM J).PosSemidef) {δ : ℝ}
    (hShift : ((tau S * (1+δ)) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM J).PosSemidef)
    (hout : preInside S C (encodedInput J) = false) : 1 < δ := by
  by_contra hn
  have hd : δ ≤ 1 := le_of_not_gt hn
  have hu := last_level (N := N) S C (show 0 < C by omega)
  have hShift' : ((candidateLevel S C (List.replicate N (), C * (N+1)) : ℝ) •
      (1 : Matrix (Fin N) (Fin N) ℝ) - castM J).PosSemidef := by
    rw [hu]
    have hh := mul_le_mul_of_nonneg_left hd (EnvelopeAnalysis.tau_pos S).le
    exact scalar_shift_mono _ (by nlinarith only [hh]) hShift
  have ht := candidatePSD_complete S C (C * (N+1)) J hC hJ (by rw [hu]) hShift'
  rw [inside_eq_candidate] at hout
  rw [ht] at hout
  contradiction

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

end CritWinSpin.Implementation.SpinKernel

end

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory IsingLTL.BeliefProp

namespace CritWinSpin.Implementation.DensityKernelTV

variable {X A : Type*} [MeasurableSpace X] [Fintype A]

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

section
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] List.flatMap
noncomputable section

end
end

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

theorem tableBits_linear (n m : ℕ) : tableBits (n, m) ≤ 4 * n * m + 1 := by
  unfold tableBits
  change (4 * n * m).size + 1 ≤ 4 * n * m + 1
  have hh : (4 * n * m).size ≤ 4 * n * m := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

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

section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option Elab.async false

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

end
end CritWinSpin.LocalTM2.Compiled.EnumerationProof

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CritWinSpin.LocalTM2.Compiled.SamplerBranchCorrectness
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC IsingLTL.BeliefProp

end CritWinSpin.LocalTM2.Compiled.SamplerBranchCorrectness

end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace CritWinSpin.Implementation.RuntimeArithmetic

theorem power_le_exp {b : ℝ} (hb : 0 ≤ b) (n : ℕ) : b ^ n ≤ Real.exp ((n:ℝ)*b) := by
  have hh : b ≤ Real.exp b := by linarith only [Real.add_one_le_exp b]
  exact (pow_le_pow_left₀ hb hh n).trans_eq (Real.exp_nat_mul b n).symm

theorem critical_coin_bound {C D X Y : ℝ} (N m cap e : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hX : 1 ≤ X) (hY : 0 ≤ Y)
    (hNX : (N:ℝ) ≤ X) (hmX : (m:ℝ) ≤ X) (hcap : (cap:ℝ) ≤ D*(Y+1)) :
    (C*((N:ℝ)+1)*((m:ℝ)*(16*(m:ℝ)*(4:ℝ)^cap)+1))^e ≤
      ((34*C)^e * Real.exp (4*(e:ℝ)*D)) * X^(3*e) *
        Real.exp ((4*(e:ℝ)*D)*Y) := by
  have hXp : 0 ≤ X := by linarith only [hX]
  have hpow : 1 ≤ (4:ℝ)^cap := one_le_pow₀ (by norm_num)
  have hX2 : 1 ≤ X^2 := one_le_pow₀ hX
  have hprod : 1 ≤ X^2*(4:ℝ)^cap := by
    have hh := mul_le_mul hX2 hpow zero_le_one (by positivity : (0:ℝ) ≤ X^2)
    simpa only [one_mul] using hh
  have hm2 := pow_le_pow_left₀ (Nat.cast_nonneg m : (0:ℝ) ≤ m) hmX 2
  have hmScaled := mul_le_mul_of_nonneg_right hm2 (show (0:ℝ) ≤ 16*(4:ℝ)^cap by positivity)
  have hmQ : (m:ℝ)*(16*(m:ℝ)*(4:ℝ)^cap)+1 ≤ 17*X^2*(4:ℝ)^cap := by
    nlinarith only [hmScaled,hprod]
  have hN1 : (N:ℝ)+1 ≤ 2*X := by linarith only [hNX,hX]
  have hBase : C*((N:ℝ)+1)*((m:ℝ)*(16*(m:ℝ)*(4:ℝ)^cap)+1) ≤
      34*C*X^3*(4:ℝ)^cap := by
    calc
      _ ≤ C*(2*X)*(17*X^2*(4:ℝ)^cap) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hN1 hC) hmQ (by positivity) (by positivity)
      _ = _ := by ring
  have hpowE : ((4:ℝ)^cap)^e ≤ Real.exp ((e:ℝ)*(4*(cap:ℝ))) := by
    have hh := pow_le_pow_left₀ (show (0:ℝ) ≤ (4:ℝ)^cap by positivity)
      (power_le_exp (by norm_num : (0:ℝ) ≤ 4) cap) e
    rw [← Real.exp_nat_mul] at hh
    simpa only [mul_comm] using hh
  have hCapE : (e:ℝ)*(4*(cap:ℝ)) ≤ (4*(e:ℝ)*D)*Y + 4*(e:ℝ)*D := by
    have hh := mul_le_mul_of_nonneg_left hcap (show (0:ℝ) ≤ 4*(e:ℝ) by positivity)
    nlinarith only [hh]
  have ht := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ C*((N:ℝ)+1)*((m:ℝ)*(16*(m:ℝ)*(4:ℝ)^cap)+1)) hBase e
  calc
    _ ≤ (34*C*X^3*(4:ℝ)^cap)^e := ht
    _ = (34*C)^e * X^(3*e) * ((4:ℝ)^cap)^e := by rw [mul_pow,mul_pow,← pow_mul]
    _ ≤ (34*C)^e * X^(3*e) * Real.exp ((e:ℝ)*(4*(cap:ℝ))) :=
      mul_le_mul_of_nonneg_left hpowE (by positivity)
    _ ≤ (34*C)^e * X^(3*e) * Real.exp ((4*(e:ℝ)*D)*Y+4*(e:ℝ)*D) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hCapE) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

theorem clock_absorption {A K E : ℝ} (d k : ℕ) (hA : 0 < A) (hK : 0 ≤ K) (hE : 0 ≤ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y coins ell T : ℝ),
      1 ≤ X → 0 ≤ Y → 0 ≤ coins → 0 ≤ ell →
      coins ≤ K*X^k*Real.exp (E*Y) → ell+1 ≤ 6*X →
      T ≤ A*(coins+ell+1)^d →
      T ≤ C*X^((k+1)*d)*Real.exp (C*Y) := by
  let P : ℝ := A*(K+6)^d
  let C : ℝ := P+E*(d:ℝ)+1
  have hP : 0 < P := by dsimp [P]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro X Y coins ell T hX hY hc0 hell hc hlen ht
  have hXp : 0 ≤ X := by linarith only [hX]
  have hExp : 1 ≤ Real.exp (E*Y) := Real.one_le_exp (mul_nonneg hE hY)
  have hp : X^k ≤ X^(k+1) := pow_le_pow_right₀ hX (Nat.le_succ k)
  have hXPow : X ≤ X^(k+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hX (show 1 ≤ k+1 by omega)
  have hCoin : coins ≤ K*X^(k+1)*Real.exp (E*Y) := hc.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hK) (Real.exp_pos _).le)
  have hLen : ell+1 ≤ 6*X^(k+1)*Real.exp (E*Y) := by
    have hh := mul_le_mul hXPow hExp zero_le_one (pow_nonneg hXp (k+1))
    have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ 6 by norm_num)
    nlinarith only [hlen,hh']
  have hSum : coins+ell+1 ≤ (K+6)*X^(k+1)*Real.exp (E*Y) := by nlinarith only [hCoin,hLen]
  have hTime : T ≤ P*X^((k+1)*d)*Real.exp ((E*(d:ℝ))*Y) := by
    calc
      _ ≤ A*(coins+ell+1)^d := ht
      _ ≤ A*((K+6)*X^(k+1)*Real.exp (E*Y))^d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hSum d) hA.le
      _ = _ := by
        rw [mul_pow,mul_pow,← pow_mul,← Real.exp_nat_mul]
        have he : (d:ℝ)*(E*Y) = (E*(d:ℝ))*Y := by ring
        rw [he]
        dsimp [P]
        ring
  have hPC : P ≤ C := by
    dsimp [C]
    have hh : (0:ℝ) ≤ E*(d:ℝ) := mul_nonneg hE (Nat.cast_nonneg d)
    linarith only [hh]
  have hEC : E*(d:ℝ) ≤ C := by dsimp [C]; linarith only [hP]
  exact hTime.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hPC (pow_nonneg hXp _))
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hEC hY))
    (Real.exp_pos _).le (by positivity))

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

theorem selected_critical_upper {N : ℕ} (S : SpinLaw) (C : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hC8 : 8 ≤ C)
    (hC : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ))
    (hJ : (castM J).PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hShift : ((tau S * (1+δ)) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM J).PosSemidef) :
    (preSelectedLevel S C (encodedInput J) : ℝ) ≤
      tau S * (1+δ) + 3 * (preBuffer (List.replicate N ()) : ℝ) := by
  let M : ℕ := C * (N+1)
  let j : ℕ := ⌈(M : ℝ) * δ⌉₊
  let idx := (preTests S C (encodedInput J)).findIdx id
  have hCp : 0 < C := by omega
  have hCR : (0 : ℝ) < C := by exact_mod_cast hCp
  have hMp : 0 < (M : ℝ) := by dsimp [M]; positivity
  have hMcast : (M : ℝ) = (C : ℝ) * ((N : ℝ)+1) := by dsimp [M]; push_cast; rfl
  have hτ := EnvelopeAnalysis.tau_pos S
  have hjM : j ≤ M := by
    apply Nat.ceil_le.mpr
    have hh := mul_le_mul_of_nonneg_left hδ1 hMp.le
    simpa only [mul_one] using hh
  have hfrL : δ ≤ (j : ℝ) / (M : ℝ) := by
    apply (le_div_iff₀ hMp).2
    have hh := Nat.le_ceil ((M : ℝ) * δ)
    change (M : ℝ) * δ ≤ (j : ℝ) at hh
    nlinarith only [hh]
  have hfrU : (j : ℝ) / (M : ℝ) ≤ δ + 1 / (M : ℝ) := by
    apply (div_le_iff₀ hMp).2
    have he : (δ + 1 / (M : ℝ)) * (M : ℝ) = δ * (M : ℝ) + 1 := by
      field_simp [hMp.ne'] <;> ring
    rw [he]
    have hh := Nat.ceil_lt_add_one (mul_nonneg hMp.le hδ)
    change (j : ℝ) < (M : ℝ) * δ + 1 at hh
    nlinarith only [hh]
  have hju : tau S * (1+δ) ≤ (candidateLevel S C (List.replicate N (), j) : ℝ) := by
    rw [candidateLevel_cast, ← hMcast]
    have hh := mul_le_mul_of_nonneg_left hfrL hτ.le
    nlinarith only [hh]
  have htest := candidatePSD_complete S C j J hC8 hJ
    (candidate_range S C j hCp hjM).2 (scalar_shift_mono _ hju hShift)
  have hidx : idx ≤ j := by
    dsimp only [idx]
    rw [selectedIndex_eq, polynomialFuel_length, List.length_replicate, pow_one]
    exact first_true_le htest
  have hidxR : (idx : ℝ) ≤ (j : ℝ) := by exact_mod_cast hidx
  have hSel : tau S * (1 + (idx : ℝ) / (M : ℝ)) ≤
      tau S * (1 + (j : ℝ) / (M : ℝ)) := by
    have hh := div_le_div_of_nonneg_right hidxR hMp.le
    have hs := mul_le_mul_of_nonneg_left hh hτ.le
    nlinarith only [hs]
  have hJup : tau S * (1 + (j : ℝ) / (M : ℝ)) ≤
      tau S * (1+δ) + tau S / (M : ℝ) := by
    calc
      _ ≤ tau S * (1 + (δ + 1 / (M : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith only [hfrU]) hτ.le
      _ = _ := by ring
  have hGrid : tau S / (M : ℝ) ≤ (preBuffer (List.replicate N ()) : ℝ) := by
    have hc : 1000 * tau S ≤ (C : ℝ) := by
      rw [fixedScale_cast] at hC
      nlinarith only [hC, hτ]
    rw [hMcast, preBuffer_cast]
    apply (div_le_div_iff₀ (by positivity : 0 < (C : ℝ) * ((N : ℝ)+1))
      (by positivity : 0 < 1000 * ((N : ℝ)+1))).2
    have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ (N : ℝ)+1 by positivity)
    nlinarith only [hh]
  have hLevel := selected_level_eq S C J
  rw [candidateLevel_cast, ← hMcast] at hLevel
  change (preSelectedLevel S C (encodedInput J) : ℝ) =
    tau S * (1 + (idx : ℝ)/(M : ℝ)) + 2 * (preBuffer (List.replicate N ()) : ℝ) at hLevel
  nlinarith only [hLevel, hSel, hJup, hGrid]

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

theorem rateI_nonneg (S : SpinLaw) (m : ℝ) : 0 ≤ rateI S m := by
  by_cases hB : BddAbove (Set.range (fun t : ℝ => t*m-phi S t))
  · have hh : (0:ℝ)*m-phi S 0 ≤ rateI S m := le_ciSup hB 0
    rw [zero_mul, EnvelopeAnalysis.phi_zero, sub_zero] at hh
    exact hh
  · unfold rateI
    rw [Real.iSup_of_not_bddAbove hB]

theorem delta_bdd (S : SpinLaw) {t : ℝ} (ht : 0 ≤ t) :
    BddAbove (Set.range (fun m : {m : ℝ // |m| ≤ 1} => (t/2)*(m:ℝ)^2-rateI S m)) := by
  refine ⟨t/2, ?_⟩
  rintro _ ⟨m,rfl⟩
  have hm : (m:ℝ)^2 ≤ 1 := by nlinarith [(abs_le.mp m.2).1, (abs_le.mp m.2).2]
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ t/2 by positivity)
  have hI := rateI_nonneg S m
  nlinarith only [hh,hI]

theorem delta_mono (S : SpinLaw) {s t : ℝ} (ht : 0 ≤ t) (hst : s ≤ t) : deltaS S s ≤ deltaS S t := by
  letI : Nonempty {m : ℝ // |m| ≤ 1} := ⟨⟨0,by norm_num⟩⟩
  unfold deltaS
  apply ciSup_le
  intro m
  have hh := mul_le_mul_of_nonneg_right hst (sq_nonneg (m:ℝ))
  exact (show (s/2)*(m:ℝ)^2-rateI S m ≤ (t/2)*(m:ℝ)^2-rateI S m by nlinarith only [hh]).trans
    (le_ciSup (delta_bdd S ht) m)

theorem buffer_smoothed (N : ℕ) : 3*(preBuffer (List.replicate N ()):ℝ) ≤
    1/(5*((N:ℝ)+1)) := by
  rw [preBuffer_cast]
  have he : 3*(1/(1000*((N:ℝ)+1))) = 3/(1000*((N:ℝ)+1)) := by ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 1000*((N:ℝ)+1))
    (by positivity : (0:ℝ) < 5*((N:ℝ)+1))).2
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith only [hn]

theorem actual_cap_budget (S : SpinLaw) (p C : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
    (hC8 : 8 ≤ C) (hC : 1000*(fixedScale S:ℝ) ≤ (C:ℝ))
    (hPrecision : 1000*integrationConstant S ≤ (C:ℝ)) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) ℚ) (δ : ℝ),
      J.IsSymm → (castM J).PosSemidef → 0 ≤ δ →
      ((tau S*(1+δ)) • (1 : Matrix (Fin N) (Fin N) ℝ)-castM J).PosSemidef →
      preInside S C (encodedInput J) = true →
      (preCap S C (encodedInput J):ℝ) ≤ D*((N:ℝ)*δ^((p:ℝ)/((p:ℝ)-1))+1) := by
  obtain ⟨D₀,hD₀,hBudget⟩ := sampler_smoothed_cap_budget S p hS hp
  obtain ⟨_,_,hDelta⟩ := lemma_4_2 S p hS hp
  have hCR : (0:ℝ) ≤ C := Nat.cast_nonneg C
  refine ⟨D₀+(C:ℝ)+1, by positivity, ?_⟩
  intro N J δ hJ hPSD hδ hShift hin
  let r : ℝ := (p:ℝ)/((p:ℝ)-1)
  let X : ℝ := (N:ℝ)*δ^r
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hX : 0 ≤ X := mul_nonneg hN (Real.rpow_nonneg hδ r)
  have hb := selected_bounds S C J hJ hC8 hC hin
  have hbuf : (0:ℝ) < preBuffer (List.replicate N ()) := by rw [preBuffer_cast]; positivity
  have hs : tau S < (preSelectedLevel S C (encodedInput J):ℝ) := by linarith only [hb.1,hbuf]
  change (preCap S C (encodedInput J):ℝ) ≤ (D₀+(C:ℝ)+1)*(X+1)
  by_cases hd1 : δ ≤ 1
  · have hLevel := selected_critical_upper S C J hC8 hC hPSD hδ hd1 hShift
    have hSmooth : (preSelectedLevel S C (encodedInput J):ℝ) ≤
        tau S*(1+δ)+1/(5*((N:ℝ)+1)) := by linarith only [hLevel,buffer_smoothed N]
    have ht : 0 ≤ tau S*(1+δ)+1/(5*((N:ℝ)+1)) := by
      have hτ := EnvelopeAnalysis.tau_pos S
      positivity
    obtain ⟨_,_,_,_,_,hDs,_⟩ := hDelta _ hs
    have hD : ds S (preSelectedLevel S C (encodedInput J)) 0 ≤
        deltaS S (tau S*(1+δ)+1/(5*((N:ℝ)+1))) :=
      (hDs 0).2.trans (delta_mono S ht hSmooth)
    have hCap := (preCap_bounds S hS C J hC8 hPrecision hs hb.2.1).2
    have hMul := mul_le_mul_of_nonneg_left hD hN
    have hBd := hBudget N 5 δ (by decide) hδ
    norm_num only [Nat.cast_ofNat] at hBd
    have hh : (preCap S C (encodedInput J):ℝ) ≤ D₀*(X+1)+1 := by
      change (N:ℝ)*deltaS S (tau S*(1+δ)+1/(5*((N:ℝ)+1)))+1 ≤ D₀*(X+1) at hBd
      linarith only [hCap,hMul,hBd]
    have hCX := mul_nonneg hCR hX
    nlinarith only [hh,hCX,hCR,hX]
  · have hd : 1 ≤ δ := (lt_of_not_ge hd1).le
    have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.1
    have hr : 0 ≤ r := by dsimp [r]; apply div_nonneg <;> linarith only [hpR]
    have hPow := Real.one_le_rpow hd hr
    have hNX : (N:ℝ)+1 ≤ X+1 := by
      have hh := mul_le_mul_of_nonneg_left hPow hN
      dsimp [X]
      nlinarith only [hh]
    have hCap := cap_fits_fuel S hS C J hJ hC8 hC hPrecision hin
    have hCapR : (preCap S C (encodedInput J):ℝ) ≤ (C:ℝ)*((N:ℝ)+1) := by exact_mod_cast hCap
    have hh := mul_le_mul_of_nonneg_left hNX hCR
    have hi := mul_le_mul_of_nonneg_right (show (C:ℝ) ≤ D₀+(C:ℝ)+1 by linarith only [hD₀])
      (show 0 ≤ X+1 by linarith only [hX])
    exact hCapR.trans (hh.trans hi)

end CritWinSpin.Implementation.CriticalCapBudget
end

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2

theorem natPolynomial_mono (P : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) :
    P.eval a ≤ P.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

theorem natPolynomial_growth (P : Polynomial ℕ) (n : ℕ) :
    P.eval n ≤ P.eval 1 * (n + 1) ^ P.natDegree := by
  have hc : (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i) = P.eval 1 := by
    rw [Polynomial.eval_eq_sum_range]
    simp
  calc
    P.eval n = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * n ^ i :=
      Polynomial.eval_eq_sum_range (p := P) n
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (n + 1) ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      apply Nat.mul_le_mul_left
      exact (Nat.pow_le_pow_left (Nat.le_succ n) i).trans
        (Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (by simpa using Finset.mem_range.mp hi))
    _ = P.eval 1 * (n + 1) ^ P.natDegree := by rw [← Finset.sum_mul, hc]

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open OAI.MetricKMedian.Binary

noncomputable def machineClockEnvelope {f : List Bool → List Bool} {c : List Bool → ℕ}
    (P : PolyProgram id id f) (C : PolyProgram id Nat.bits c) : Polynomial ℕ :=
  P.time.comp (2 * Polynomial.X + 4) + (C.comp encBinProgram).time + Polynomial.X

theorem machineClockEnvelope_bounds {f : List Bool → List Bool} {c : List Bool → ℕ}
    (P : PolyProgram id id f) (C : PolyProgram id Nat.bits c) (x : List Bool) :
    (programRandMachine P C).time x ≤ (machineClockEnvelope P C).eval (c x + x.length) := by
  change max (P.time.eval (2 * (c x + x.length) + 4))
    (max ((C.comp encBinProgram).time.eval x.length) (c x)) ≤ _
  simp only [machineClockEnvelope, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  have hq := natPolynomial_mono (C.comp encBinProgram).time
    (Nat.le_add_left x.length (c x))
  apply max_le
  · omega
  · apply max_le <;> omega

theorem programRandMachine_growth {f : List Bool → List Bool} {c : List Bool → ℕ}
    (P : PolyProgram id id f) (C : PolyProgram id Nat.bits c) :
    ∃ A d : ℕ, 0 < A ∧ ∀ x, (programRandMachine P C).time x ≤
      A * (c x + x.length + 1) ^ d := by
  let H := machineClockEnvelope P C
  refine ⟨H.eval 1 + 1, H.natDegree, by omega, ?_⟩
  intro x
  exact (machineClockEnvelope_bounds P C x).trans
    ((natPolynomial_growth H (c x + x.length)).trans
      (Nat.mul_le_mul_right _ (Nat.le_succ _)))

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

theorem enumeration_budget_bound (S : SpinLaw) (N m : ℕ) (X : ℝ)
    (hX : 1 ≤ X) (hmX : (m : ℝ) ≤ X) :
    (budgetFromPowers ((alphabet S).length ^ N,
      ((alphabet S).length * weightDenominatorBound S) ^ N, m) : ℝ) ≤
      8200 * X ^ 3 * Real.exp
        (3 * ((alphabet S).length + (alphabet S).length * weightDenominatorBound S + 1 : ℕ) * (N : ℝ)) := by
  let q := (alphabet S).length
  let v := q * weightDenominatorBound S
  let B : ℝ := 3 * ((q : ℝ) + v + 1)
  let Z : ℝ := Real.exp (B * N)
  have hXp : 0 ≤ X := by linarith only [hX]
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hX
  have hm3 : (m : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmX 3
  have hXpow : X ≤ X ^ 3 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hX (show 1 ≤ 3 by decide))
  have hm3' : (m : ℝ) ≤ X ^ 3 := hmX.trans hXpow
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 1 ≤ Z := Real.one_le_exp (mul_nonneg hB (Nat.cast_nonneg N))
  have hq : ((q ^ N : ℕ) : ℝ) ≤ Z := by
    have hh := power_le_exp (Nat.cast_nonneg q : (0 : ℝ) ≤ q) N
    have hb : (q : ℝ) ≤ B := by dsimp [B]; nlinarith only [hq0,hv0]
    have hqq : ((q ^ N : ℕ) : ℝ) ≤ Real.exp ((N : ℝ) * q) := by
      simpa only [Nat.cast_pow] using hh
    exact hqq.trans (Real.exp_le_exp.mpr (by nlinarith only [hb,hN0]))
  have hv : (((v ^ N : ℕ) : ℝ)) ^ 3 ≤ Z := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (v : ℝ) ^ N)
      (power_le_exp (Nat.cast_nonneg v : (0 : ℝ) ≤ v) N) 3
    rw [← Real.exp_nat_mul] at hh
    have hb : 3 * (v : ℝ) ≤ B := by dsimp [B]; nlinarith only [hq0]
    have hvv : (((v ^ N : ℕ) : ℝ)) ^ 3 ≤ Real.exp (3 * ((N : ℝ) * v)) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
    exact hvv.trans (Real.exp_le_exp.mpr (by nlinarith only [hb,hN0]))
  have ht : (tableBits (q ^ N, m) : ℝ) ≤ 4 * (q ^ N : ℕ) * m + 1 := by
    exact_mod_cast tableBits_linear (q ^ N) m
  have hnZ : ((q ^ N : ℕ) : ℝ) ≤ X ^ 3 * Z := hq.trans
    (by nlinarith only [hX3, show (0 : ℝ) ≤ Z by positivity])
  have hnmZ : ((q ^ N : ℕ) : ℝ) * m ≤ X ^ 3 * Z := by
    exact (mul_le_mul hq hm3' (Nat.cast_nonneg m) (show (0 : ℝ) ≤ Z by positivity)).trans_eq (mul_comm _ _)
  have hmvZ : (m : ℝ) ^ 3 * (((v ^ N : ℕ) : ℝ)) ^ 3 ≤ X ^ 3 * Z :=
    mul_le_mul hm3 hv (by positivity) (pow_nonneg hXp 3)
  have hOne : 1 ≤ X ^ 3 * Z := by nlinarith only [hX3, hZ]
  change _ ≤ 8200 * X ^ 3 * Real.exp (3 * ((q + v + 1 : ℕ) : ℝ) * (N : ℝ))
  have he : Real.exp (3 * ((q + v + 1 : ℕ) : ℝ) * (N : ℝ)) = Z := by simp only [Z, B, Nat.cast_add, Nat.cast_one]
  rw [he]
  change (budgetFromPowers (q ^ N, v ^ N, m) : ℝ) ≤ _
  simp only [budgetFromPowers, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hp : (2 : ℝ) * (16 * m * (v : ℝ) ^ N) ^ 3 =
      8192 * (m : ℝ) ^ 3 * ((v : ℝ) ^ N) ^ 3 := by ring
  rw [hp]
  simp only [Nat.cast_pow] at ht hnZ hnmZ hmvZ
  nlinarith only [ht, hnZ, hnmZ, hmvZ, hOne]

theorem quoted_length (xs : List Bool) :
    (xs.flatMap (fun b => [true,b])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem encoded_input_length {N : ℕ} (I : Inst N) (m : ℕ) :
    (tupleCode [encInst I, encBin m]).length ≤ 2 * bitLen I + 4 * m + 8 := by
  have hb : m.bits.length ≤ m := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have he : (encBin m).length = 2 * m.bits.length + 2 := by
    simp only [encBin, List.length_append, quoted_length, List.length_cons, List.length_nil]
  rw [tupleCode_pair_length, he]
  change 2 * ((encInst I).length + (2 * m.bits.length + 2)) + 4 ≤ _
  change _ ≤ 2 * (encInst I).length + 4 * m + 8
  omega

theorem critical_coins_formula {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C m : ℕ)
    (J : Matrix (Fin N) (Fin N) ℚ) (hJ : J.IsSymm) (hC8 : 8 ≤ C)
    (hC : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ))
    (hPrecision : 1000 * integrationConstant S ≤ (C : ℝ))
    (hin : preInside S C (encodedInput J) = true) :
    criticalCoins S C (encodedInput J,m) =
      (C * (N+1) * (m * (16 * m * 4 ^ preCap S C (encodedInput J)) + 1)) ^ 1000000 := by
  rw [criticalCoins, uniformBudget, baseBudget, retryCount_formula S hS C m J hJ hC8 hC hPrecision hin]
  simp only [encodedInput, List.length_replicate]
  rw [← pow_mul]

theorem _root_.solution (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
    (C : ℕ) (hC8 : 8 ≤ C) (hC : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ))
    (hPrecision : 1000 * integrationConstant S ≤ (C : ℝ)) :
    ∃ (Ctime : ℝ) (k : ℕ), 0 < Ctime ∧ ∀ (N : ℕ) (I : Inst N) (m : ℕ) (δ : ℝ),
      I.1.IsSymm → (castM I.1).PosSemidef → 0 ≤ δ →
      ((tau S*(1+δ)) • (1 : Matrix (Fin N) (Fin N) ℝ)-castM I.1).PosSemidef → 5 ≤ m →
      ((criticalWindowMachine S C).time (tupleCode [encInst I, encBin m]) : ℝ) ≤
        Ctime * ((N : ℝ) + bitLen I + m) ^ k *
          Real.exp (Ctime * N * δ ^ ((p : ℝ) / ((p : ℝ)-1))) := by
  obtain ⟨D,hD,hCap⟩ := CriticalCapBudget.actual_cap_budget S p C hS hp hC8 hC hPrecision
  obtain ⟨A,d,hA,hTime⟩ := programRandMachine_growth (finalSamplerProgram S C) (finalCoinProgram S C)
  let e : ℕ := 1000000
  let kCoin : ℕ := 3000000
  let Kcrit : ℝ := (34*(C:ℝ)) ^ e * Real.exp (4*(e:ℝ)*D)
  let Ecrit : ℝ := 4*(e:ℝ)*D
  let B : ℝ := 3*((alphabet S).length + (alphabet S).length * weightDenominatorBound S + 1 : ℕ)
  let K : ℝ := Kcrit + 8200 + 1
  let E : ℝ := Ecrit + B + 1
  have hCR : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hKcrit : 0 ≤ Kcrit := by dsimp [Kcrit]; positivity
  have hEcrit : 0 ≤ Ecrit := by dsimp [Ecrit]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  obtain ⟨Ctime,hCtime,hClock⟩ := clock_absorption d kCoin hAR hK hE
  refine ⟨Ctime,(kCoin+1)*d,hCtime,?_⟩
  intro N I m δ hI hPSD hδ hShift hm
  let X : ℝ := (N : ℝ) + bitLen I + m
  let Y : ℝ := (N : ℝ) * δ ^ ((p : ℝ) / ((p : ℝ)-1))
  let xs := tupleCode [encInst I, encBin m]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbit0 : (0 : ℝ) ≤ bitLen I := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hXp : 0 ≤ X := by dsimp [X]; positivity
  have hX : 1 ≤ X := by
    have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp [X]
    linarith only [hmR,hN0,hbit0]
  have hNX : (N : ℝ) ≤ X := by dsimp [X]; linarith only [hbit0,hm0]
  have hmX : (m : ℝ) ≤ X := by dsimp [X]; linarith only [hN0,hbit0]
  have hY : 0 ≤ Y := mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hδ _)
  have hcoins : ((criticalWindowMachine S C).coins xs : ℝ) ≤ K * X ^ kCoin * Real.exp (E*Y) := by
    have hc := criticalWindowMachine_coins_encoded S C I m
    change (criticalWindowMachine S C).coins xs =
      (if (List.replicate N ()).isEmpty then 0 else
        if preInside S C (encodedInput I.1) then criticalCoins S C (encodedInput I.1,m)
        else enumerationBudget S ((instanceListModel I,List.replicate N ()),m)) at hc
    by_cases hN : N = 0
    · subst N
      simp only [List.replicate_zero, List.isEmpty_nil, ite_true] at hc
      rw [hc]
      simp only [Nat.cast_zero]
      positivity
    · have hempty : (List.replicate N ()).isEmpty = false := by cases N <;> simp_all
      rw [hempty] at hc
      cases hin : preInside S C (encodedInput I.1) with
      | true =>
        simp only [hin, ite_true, Bool.true_eq_false, Bool.false_eq_true, ite_false] at hc
        rw [hc, critical_coins_formula S hS C m I.1 hI hC8 hC hPrecision hin]
        have hcap := hCap N I.1 δ hI hPSD hδ hShift hin
        have ht := critical_coin_bound (C := (C : ℝ)) (D := D) (X := X) (Y := Y)
          N m (preCap S C (encodedInput I.1)) e hCR hD.le hX hY hNX hmX hcap
        have ht' : (((C * (N+1) * (m * (16*m*4 ^ preCap S C (encodedInput I.1)) + 1)) ^ 1000000 : ℕ) : ℝ) ≤
            (Kcrit * X ^ kCoin * Real.exp (Ecrit*Y) : ℝ) := by
          simpa only [Nat.cast_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,e,kCoin,Kcrit,Ecrit] using ht
        have hKK : Kcrit ≤ K := by dsimp [K]; linarith
        have hEE : Ecrit ≤ E := by dsimp [E]; linarith only [hB]
        exact ht'.trans (mul_le_mul
          (mul_le_mul_of_nonneg_right hKK (pow_nonneg hXp kCoin))
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hEE hY))
          (Real.exp_pos _).le (mul_nonneg hK (pow_nonneg hXp kCoin)))
      | false =>
        simp only [hin, Bool.false_eq_true, ite_false] at hc
        rw [hc]
        have hbudget : enumerationBudget S ((instanceListModel I,List.replicate N ()),m) =
            budgetFromPowers ((alphabet S).length ^ N,
              ((alphabet S).length * weightDenominatorBound S) ^ N,m) := by
          simp only [enumerationBudget,List.map_replicate,naturalProduct_eq,List.prod_replicate]
        rw [hbudget]
        have hd1 := inside_false_supercritical S C I.1 hC8 hPSD hShift hin
        have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.1
        have hr : 0 ≤ (p : ℝ) / ((p : ℝ)-1) := by apply div_nonneg <;> linarith only [hpR]
        have hpow := Real.one_le_rpow hd1.le hr
        have hNY : (N : ℝ) ≤ Y := by
          dsimp [Y]
          have hh := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
          simpa only [mul_one] using hh
        have ht := enumeration_budget_bound S N m X hX hmX
        change _ ≤ 8200 * X ^ 3 * Real.exp (B*N) at ht
        have hKK : (8200 : ℝ) ≤ K := by dsimp [K]; linarith only [hKcrit]
        have hXE : X ^ 3 ≤ X ^ kCoin := pow_le_pow_right₀ hX (by dsimp [kCoin]; omega)
        have hBE : B ≤ E := by dsimp [E]; linarith only [hEcrit]
        have hpoly := mul_le_mul hKK hXE (pow_nonneg hXp 3) hK
        have hexp : Real.exp (B*N) ≤ Real.exp (E*Y) := Real.exp_le_exp.mpr
          (mul_le_mul hBE hNY (Nat.cast_nonneg N) hE)
        exact ht.trans (mul_le_mul hpoly hexp (Real.exp_pos _).le
          (mul_nonneg hK (pow_nonneg hXp kCoin)))
  have hlen : ((xs.length : ℕ) : ℝ) + 1 ≤ 6*X := by
    have hh : (xs.length : ℝ) ≤ 2*bitLen I + 4*m + 8 := by exact_mod_cast encoded_input_length I m
    have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp [X]
    linarith only [hh,hmR,hN0,hbit0]
  have ht : ((criticalWindowMachine S C).time xs : ℝ) ≤
      (A : ℝ) * (((criticalWindowMachine S C).coins xs : ℝ) + xs.length + 1) ^ d := by
    have hh := hTime xs
    change (criticalWindowMachine S C).time xs ≤ A * ((criticalWindowMachine S C).coins xs + xs.length + 1) ^ d at hh
    exact_mod_cast hh
  have hfinal := hClock X Y ((criticalWindowMachine S C).coins xs) xs.length
    ((criticalWindowMachine S C).time xs) hX hY (Nat.cast_nonneg _) (Nat.cast_nonneg _) hcoins hlen ht
  simpa only [X,Y,xs,mul_assoc] using hfinal

end CritWinSpin.Implementation.SamplerRuntime
end

end

section

set_option autoImplicit false
noncomputable section

namespace CritWinSpin.Implementation.SamplerConstantChoice
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled

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

end

end
