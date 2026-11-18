-- Prove2me | solution 1 for CritWinSpin.rounded_euler_weak_budget
-- status  : ACCEPTED   (prove)
-- author  : @Maxliu
-- created : 2026-11-17T18:23:55.892532+00:00
-- url     : https://prove2.me/submissions/9e1dae6e-a923-46a3-90b0-fc07436b78e6

import Definitions.Def_CritWinSpin_SamplerNumericalData
import Theorems.Thm_CritWinSpin_langevin_weak_budget

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

def drift (g : E → E) (γ : ℝ) (x : E) : E := x - γ • g x



























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

theorem bounded_integrable {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ} {B L : ℝ} (hf : BoundedLip f B L) : Integrable f μ := by
  refine (integrable_const B).mono' hf.1.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hf.2.1 x

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
  apply CritWinSpin.langevin_weak_budget d cert.U cert.g (DensityAnalysis.gibbs cert.U) rfl a s e R
    cert.continuous_U cert.continuous_g cert.density_integrable cert.monotone cert.taylor
    cert.lipschitz cert.grad_integrable cert.norm_integrable ha hs hs1 he0 hsmall hstep
    hR haR hsR he hM hH Q hQ hQC ?_ f B L hL hLR hf.1 hf.2.1 hf.2.2 n hn
  intro v B L hLv hv hvB hvL x
  exact happrox v B L hLv ⟨hv,hvB,hvL⟩ x

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



theorem drawIndex_expectation {n : ℕ} (L : ℕ) (cs : Fin n → ℕ)
    (htotal : ∑ i, cs i = 2 ^ L) (f : Fin n → ℝ) :
    (1 / (2 : ℝ) ^ L) *
        (∑ ω : Fin L → Bool, f (FiniteTicket.drawIndex L cs htotal ω)) =
      ∑ i, f i * ((cs i : ℝ) / (2 : ℝ) ^ L) := by
  classical
  have hpoint (ω : Fin L → Bool) :
      f (FiniteTicket.drawIndex L cs htotal ω) =
        ∑ i, f i * if FiniteTicket.drawIndex L cs htotal ω = i then (1 : ℝ) else 0 := by
    simp
  simp_rw [hpoint]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  have hh := FiniteTicket.drawIndex_law L cs htotal i
  calc
    _ = f i * ((1 / (2 : ℝ) ^ L) * ∑ ω : Fin L → Bool,
      if FiniteTicket.drawIndex L cs htotal ω = i then (1 : ℝ) else 0) := by ring
    _ = _ := by rw [hh]



end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory
noncomputable section



theorem realRound_measurable (d : ℝ) : Measurable (realRound d) := by
  unfold realRound
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
  · exact measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (Nat.measurable_floor.comp (measurable_id.neg.div_const d)))
  · exact measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (Nat.measurable_floor.comp (measurable_id.div_const d)))

theorem realRound_error (d : ℝ) (hd : 0 < d) (x : ℝ) : |realRound d x - x| ≤ d := by
  unfold realRound
  split_ifs with hx
  · have hq : 0 ≤ -x / d := div_nonneg (neg_nonneg.mpr hx.le) hd.le
    have hlo := Nat.floor_le hq
    have hhi := (Nat.lt_floor_add_one (-x / d)).le
    have hlo' := (le_div_iff₀ hd).mp hlo
    have hhi' := (div_le_iff₀ hd).mp hhi
    rw [abs_of_nonneg (by nlinarith : 0 ≤ -d * (⌊-x / d⌋₊ : ℝ) - x)]
    nlinarith
  · have hq : 0 ≤ x / d := div_nonneg (le_of_not_gt hx) hd.le
    have hlo := Nat.floor_le hq
    have hhi := (Nat.lt_floor_add_one (x / d)).le
    have hlo' := (le_div_iff₀ hd).mp hlo
    have hhi' := (div_le_iff₀ hd).mp hhi
    rw [abs_of_nonpos (by nlinarith : d * (⌊x / d⌋₊ : ℝ) - x ≤ 0)]
    nlinarith

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



theorem roundPoint_measurable (N : ℕ) (d : ℝ) : Measurable (@roundPoint N d) := by
  apply (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp
  apply measurable_pi_lambda
  intro i
  exact (realRound_measurable d).comp (by fun_prop)

theorem roundPoint_error {N : ℕ} (d : ℝ) (hd : 0 < d) (z : EuclideanSpace ℝ (Fin N)) :
    ‖roundPoint d z - z‖ ≤ ((N : ℝ) + 1) * d := by
  have hpoint (i : Fin N) : (roundPoint d z i - z i) ^ 2 ≤ d ^ 2 := by
    have he := realRound_error d hd (z i)
    change |roundPoint d z i - z i| ≤ d at he
    nlinarith [sq_abs (roundPoint d z i - z i), abs_nonneg (roundPoint d z i - z i)]
  have hs : ‖roundPoint d z - z‖ ^ 2 ≤ (N : ℝ) * d ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [PiLp.sub_apply, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hb : (N : ℝ) * d ^ 2 ≤ (((N : ℝ) + 1) * d) ^ 2 := by
    nlinarith [mul_nonneg hN (sq_nonneg d), mul_nonneg (sq_nonneg (N : ℝ)) (sq_nonneg d)]
  have hp : 0 ≤ ((N : ℝ) + 1) * d := by positivity
  nlinarith [norm_nonneg (roundPoint d z - z)]

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






























theorem approximateGradient_error {N : ℕ} (S : SpinLaw) (hS : IsGHS S)
    (L : Matrix (Fin N) (Fin N) ℚ) (h z : Fin N → ℚ) (s a d : ℚ)
    (hs : tau S < (s : ℝ)) (hd : 0 < d) (hd1 : d ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) (hL : ∀ i j, |(L i j : ℝ)| ≤ B) (i : Fin N) :
    |(approximateGradient S L h z s a d i : ℝ) -
      CritWinSpin.Implementation.EnvelopeGeometry.grad S s a (castM L) (castV h) (castV z) i| ≤
        (N : ℝ) * B * (2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ)) := by
  let E : ℝ := 2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ)
  have hE : 0 ≤ E := by
    have hp : (0 : ℝ) < (S.ρ 1 : ℝ) := by exact_mod_cast S.pos 1 S.one_mem
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd
    dsimp [E]
    positivity
  have heq : (approximateGradient S L h z s a d i : ℝ) -
      CritWinSpin.Implementation.EnvelopeGeometry.grad S s a (castM L) (castV h) (castV z) i =
      -(∑ j, (L j i : ℝ) * ((modifiedDerivativeApprox S s (L.mulVec z j + h j) d : ℝ) -
        deriv (phis S s) ((L.mulVec z j + h j : ℚ) : ℝ))) := by
    simp only [approximateGradient, CritWinSpin.Implementation.EnvelopeGeometry.grad,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_sum,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, castM, castV, Finset.sum_sub_distrib, mul_sub,
      Rat.cast_sum, Matrix.map_apply]
    try simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_mul]
    ring
  rw [heq, abs_neg]
  calc
    _ ≤ ∑ j, |(L j i : ℝ) *
        ((modifiedDerivativeApprox S s (L.mulVec z j + h j) d : ℝ) -
          deriv (phis S s) ((L.mulVec z j + h j : ℚ) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, B * E := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hL j i) (modifiedDerivativeApprox_error S hS s
        (L.mulVec z j + h j) d hs hd hd1) (abs_nonneg _) hB
    _ = _ := by simp [E]; ring



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

theorem rationalRound_measurable (d : ℚ) : Measurable (rationalRound d) := by
  unfold rationalRound
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
  · exact measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n : ℚ))).comp
      (Nat.measurable_floor.comp (measurable_id.neg.div_const (d : ℝ))))
  · exact measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n : ℚ))).comp
      (Nat.measurable_floor.comp (measurable_id.div_const (d : ℝ))))



theorem rationalProject_measurable (N : ℕ) (d : ℚ) : Measurable (@rationalProject N d) := by
  apply measurable_pi_lambda
  intro i
  exact (rationalRound_measurable d).comp (by fun_prop)

theorem rationalProject_point {N : ℕ} (d : ℚ) (z : Point N) :
    WithLp.toLp 2 (castV (rationalProject d z)) = roundPoint (d : ℝ) z := by
  ext i
  exact rationalRound_cast d (z i)



theorem rationalDrift_measurable {N : ℕ} (S : SpinLaw) (L : Matrix (Fin N) (Fin N) ℚ)
    (h : Fin N → ℚ) (s a d snap : ℚ) : Measurable (rationalDrift S L h s a d snap) :=
  (measurable_of_countable (fun q : Fin N → ℚ =>
    WithLp.toLp 2 (castV (approximateGradient S L h q s a d)))).comp
      (rationalProject_measurable N snap)

theorem norm_le_coordinate_bound {N : ℕ} (z : Point N) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ i, |z i| ≤ C) : ‖z‖ ≤ ((N : ℝ) + 1) * C := by
  have hsq (i : Fin N) : z i ^ 2 ≤ C ^ 2 := by
    nlinarith [sq_abs (z i), abs_nonneg (z i), hz i]
  have hs : ‖z‖ ^ 2 ≤ (N : ℝ) * C ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hsq i)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hb : (N : ℝ) * C ^ 2 ≤ (((N : ℝ) + 1) * C) ^ 2 := by
    nlinarith [mul_nonneg hN (sq_nonneg C), mul_nonneg (sq_nonneg (N : ℝ)) (sq_nonneg C)]
  have hp : 0 ≤ ((N : ℝ) + 1) * C := by positivity
  nlinarith [norm_nonneg z]

theorem rationalDrift_error {N : ℕ} (S : SpinLaw) (hS : IsGHS S)
    (L : Matrix (Fin N) (Fin N) ℚ) (h : Fin N → ℚ) (s a d snap : ℚ)
    (hs : tau S < (s : ℝ)) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hPSD : ((s : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) -
      castM L * (castM L).transpose).PosSemidef)
    (hd : 0 < d) (hd1 : d ≤ 1) (hsnap : 0 < snap)
    (B : ℝ) (hB : 0 ≤ B) (hL : ∀ i j, |(L i j : ℝ)| ≤ B) (z : Point N) :
    ‖rationalDrift S L h s a d snap z - gradient S s a (castM L) (castV h) z‖ ≤
      ((N : ℝ) + 1) *
        ((N : ℝ) * B * (2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ)) + 2 * snap) := by
  let q := rationalProject snap z
  let y : Point N := WithLp.toLp 2 (castV q)
  let E : ℝ := 2 * (Fintype.card {a : ℚ // a ∈ S.A} : ℝ) * d / (S.ρ 1 : ℝ)
  have hE : 0 ≤ E := by
    have hp : (0 : ℝ) < (S.ρ 1 : ℝ) := by exact_mod_cast S.pos 1 S.one_mem
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd
    dsimp [E]
    positivity
  have hq : ‖rationalDrift S L h s a d snap z - gradient S s a (castM L) (castV h) y‖ ≤
      ((N : ℝ) + 1) * ((N : ℝ) * B * E) := by
    apply norm_le_coordinate_bound _ _ (by positivity)
    intro i
    exact approximateGradient_error S hS L h q s a d hs hd hd1 B hB hL i
  have hgeom := (regular_geometry S hS (s := (s : ℝ)) (a := (a : ℝ)) hs (by exact_mod_cast ha)
    (by exact_mod_cast ha1) (castM L) (castV h) hPSD).2.1 y z
  have hy : y = roundPoint (snap : ℝ) z := rationalProject_point snap z
  have hry := roundPoint_error (snap : ℝ) (by exact_mod_cast hsnap) z
  rw [← hy] at hry
  have ht := dist_triangle (rationalDrift S L h s a d snap z)
    (gradient S s a (castM L) (castV h) y) (gradient S s a (castM L) (castV h) z)
  simp only [dist_eq_norm] at ht
  nlinarith







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

def truncationSet (R : ℝ) : Set ℝ := Set.Icc (-R) R

theorem truncated_mean_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) (K R V : ℝ) (hK : 0 ≤ K) (hR : 0 < R)
    (hx2 : Integrable (fun x : ℝ => x ^ 2) μ) (hmoment : ∫ x, x ^ 2 ∂μ ≤ V)
    (hpoint : ∀ x, |f x| ≤ K * |x|) (hZ : 0 < μ.real (truncationSet R)) :
    |(∫ x, f x ∂μ) - (∫ x in truncationSet R, f x ∂μ) / μ.real (truncationSet R)| ≤
      2 * K * V / R := by
  let S := truncationSet R
  have hs : MeasurableSet S := measurableSet_Icc
  have ht (x : ℝ) (hx : x ∈ Sᶜ) : R < |x| := by
    by_contra he
    exact hx (abs_le.mp (le_of_not_gt he))
  have htailMoment : (∫ x in Sᶜ, x ^ 2 ∂μ) ≤ V :=
    (setIntegral_le_integral hx2 (Filter.Eventually.of_forall (fun x => sq_nonneg x))).trans hmoment
  have htailProb : μ.real Sᶜ ≤ V / R ^ 2 := by
    calc
      μ.real Sᶜ = ∫ _ in Sᶜ, (1 : ℝ) ∂μ := by simp
      _ ≤ ∫ x in Sᶜ, (1 / R ^ 2) * x ^ 2 ∂μ := by
        apply integral_mono_ae (integrable_const 1) ((hx2.const_mul (1 / R ^ 2)).restrict)
        filter_upwards [self_mem_ae_restrict hs.compl] with x hx
        have hp := pow_le_pow_left₀ hR.le (ht x hx).le 2
        rw [sq_abs] at hp
        have hr2 : 0 < R ^ 2 := sq_pos_of_pos hR
        rw [one_div_mul_eq_div, le_div_iff₀ hr2]
        simpa only [one_mul] using hp
      _ = (1 / R ^ 2) * ∫ x in Sᶜ, x ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ (1 / R ^ 2) * V := mul_le_mul_of_nonneg_left htailMoment (by positivity)
      _ = V / R ^ 2 := by ring
  have htailF : |∫ x in Sᶜ, f x ∂μ| ≤ (K / R) * V := by
    calc
      _ ≤ ∫ x in Sᶜ, ‖f x‖ ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := f)
      _ ≤ ∫ x in Sᶜ, (K / R) * x ^ 2 ∂μ := by
        apply integral_mono_ae hf.norm.restrict ((hx2.const_mul (K / R)).restrict)
        filter_upwards [self_mem_ae_restrict hs.compl] with x hx
        have hp : |x| ≤ x ^ 2 / R := by
          rw [le_div_iff₀ hR]
          have hh := mul_le_mul_of_nonneg_right (ht x hx).le (abs_nonneg x)
          nlinarith [sq_abs x]
        have hh := (hpoint x).trans (mul_le_mul_of_nonneg_left hp hK)
        simpa only [Real.norm_eq_abs, div_mul_eq_mul_div, mul_div_assoc] using hh
      _ = (K / R) * ∫ x in Sᶜ, x ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ (K / R) * V := mul_le_mul_of_nonneg_left htailMoment (by positivity)
  have hinsideF : |∫ x in S, f x ∂μ| ≤ (K * R) * μ.real S := by
    have hh := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := S)
      (f := f) (C := K * R) (measure_lt_top μ S) (by
        intro x hx
        have hle : |x| ≤ R := abs_le.mpr hx
        simpa only [Real.norm_eq_abs] using
          (hpoint x).trans (mul_le_mul_of_nonneg_left hle hK))
    simpa only [Real.norm_eq_abs] using hh
  have hmass : μ.real S + μ.real Sᶜ = 1 := by
    have hh := integral_add_compl hs (integrable_const (1 : ℝ) (μ := μ))
    simpa using hh
  have hsum := integral_add_compl hs hf
  have hZ0 : μ.real S ≠ 0 := hZ.ne'
  have hnon : 0 ≤ 1 - μ.real S := by
    have hh : 0 ≤ μ.real Sᶜ := measureReal_nonneg
    linarith
  have hid : (∫ x, f x ∂μ) - (∫ x in S, f x ∂μ) / μ.real S =
      (∫ x in Sᶜ, f x ∂μ) - (∫ x in S, f x ∂μ) * (1 - μ.real S) / μ.real S := by
    rw [← hsum]
    field_simp
    ring
  have hcorrection : |(∫ x in S, f x ∂μ) * (1 - μ.real S) / μ.real S| ≤
      K * R * (1 - μ.real S) := by
    rw [abs_div, abs_mul, abs_of_nonneg hnon, abs_of_pos hZ, div_le_iff₀ hZ]
    nlinarith [mul_le_mul_of_nonneg_right hinsideF hnon]
  have hprob : 1 - μ.real S ≤ V / R ^ 2 := by linarith
  change |(∫ x, f x ∂μ) - (∫ x in S, f x ∂μ) / μ.real S| ≤ _
  rw [hid]
  have htri := abs_sub_le (∫ x in Sᶜ, f x ∂μ) 0
    ((∫ x in S, f x ∂μ) * (1 - μ.real S) / μ.real S)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  have hscaled := mul_le_mul_of_nonneg_left hprob (show 0 ≤ K * R by positivity)
  have heq : (K / R) * V + K * R * (V / R ^ 2) = 2 * K * V / R := by
    field_simp
    ring
  rw [← heq]
  nlinarith

theorem gaussianTwo_second_moment : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 2 = 2 := by
  have hh := variance_fun_id_gaussianReal (μ := 0) (v := 2)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hh
  simpa using hh

theorem gaussianTwo_sq_integrable : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 2) := by
  exact (memLp_id_gaussianReal (μ := 0) (v := 2) 2).integrable_sq

end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal

namespace CritWinSpin.Implementation.GaussianGrid

def weight (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 4)

theorem weight_continuous : Continuous weight := by unfold weight; fun_prop
theorem weight_pos (x : ℝ) : 0 < weight x := Real.exp_pos _
theorem weight_le_one (x : ℝ) : weight x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg x]

theorem weight_derivative (x : ℝ) : HasDerivAt weight ((-x / 2) * weight x) x := by
  have hh := ((((hasDerivAt_id' x).pow 2).neg).div_const 4).exp
  change HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 4)) ((-x / 2) * Real.exp (-x ^ 2 / 4)) x
  refine hh.congr_deriv ?_
  norm_num
  ring

theorem weight_derivative_bound (x : ℝ) : |deriv weight x| ≤ 1 := by
  rw [(weight_derivative x).deriv, abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2),
    abs_of_pos (weight_pos x)]
  have he : |x| / 2 ≤ Real.exp (x ^ 2 / 4) := by
    have h := Real.add_one_le_exp (x ^ 2 / 4)
    nlinarith [sq_nonneg (|x| / 2 - 1 / 2), sq_abs x]
  have hp := mul_le_mul_of_nonneg_right he (weight_pos x).le
  have hz : Real.exp (x ^ 2 / 4) * weight x = 1 := by
    rw [weight, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  exact hp.trans_eq hz

theorem weight_lipschitz : LipschitzWith 1 weight := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (weight_derivative x).differentiableAt)
  intro x
  exact_mod_cast weight_derivative_bound x

theorem normalizer_lower {R : ℝ} (hR : 1 ≤ R) : (3 / 2 : ℝ) ≤ ∫ x in (-R)..R, weight x := by
  have hpoint : ∀ x ∈ Set.Icc (-1 : ℝ) 1, (3 / 4 : ℝ) ≤ weight x := by
    intro x hx
    have hsq : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    have he := Real.add_one_le_exp (-x ^ 2 / 4)
    change (3 / 4 : ℝ) ≤ Real.exp (-x ^ 2 / 4)
    linarith
  have hm := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ : ℝ => (3 / 4 : ℝ))
    (g := weight) (a := -1) (b := 1) (by norm_num) intervalIntegrable_const
    (weight_continuous.intervalIntegrable _ _) hpoint
  have hh := intervalIntegral.integral_mono_interval (μ := volume) (f := weight)
    (a := -1) (b := 1) (c := -R) (d := R) (by linarith) (by norm_num) hR
    (Filter.Eventually.of_forall fun x => (weight_pos x).le) (weight_continuous.intervalIntegrable _ _)
  norm_num at hm
  exact hm.trans hh

theorem centered_bound {f : ℝ → ℝ} {L R : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) (hf0 : f 0 = 0)
    (x : ℝ) (hx : x ∈ Set.Icc (-R) R) : |f x| ≤ L * R := by
  have hh := hf x 0
  rw [hf0, sub_zero, sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hx) hL)

theorem product_modulus {f : ℝ → ℝ} {L R : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) (hf0 : f 0 = 0)
    (x y : ℝ) (hx : x ∈ Set.Icc (-R) R) (hy : y ∈ Set.Icc (-R) R) :
    |f x * weight x - f y * weight y| ≤ L * (1 + R) * |x - y| := by
  have hg : |weight x - weight y| ≤ |x - y| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using weight_lipschitz.dist_le_mul x y
  have hfy := centered_bound hL hf hf0 y hy
  have he : f x * weight x - f y * weight y =
      (f x - f y) * weight x + f y * (weight x - weight y) := by ring
  rw [he]
  calc
    _ ≤ |(f x - f y) * weight x| + |f y * (weight x - weight y)| := abs_add_le _ _
    _ = |f x - f y| * weight x + |f y| * |weight x - weight y| := by
      rw [abs_mul, abs_mul, abs_of_pos (weight_pos x)]
    _ ≤ (L * |x - y|) * 1 + (L * R) * |x - y| :=
      add_le_add (mul_le_mul (hf x y) (weight_le_one x) (weight_pos x).le (by positivity))
        (mul_le_mul hfy hg (abs_nonneg _) (mul_nonneg hL hR))
    _ = _ := by ring

theorem ratio_error {Z Z' A A' M u v : ℝ} (hZ : 0 < Z) (hZ' : 1 ≤ Z')
    (hM : 0 ≤ M) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hMass : |Z' - Z| ≤ u) (hA : |A| ≤ M * Z) (hNum : |A' - A| ≤ v) :
    |A' / Z' - A / Z| ≤ v + M * u := by
  have hZp : 0 < Z' := by linarith
  rw [div_sub_div _ _ hZp.ne' hZ.ne', abs_div, abs_of_pos (mul_pos hZp hZ)]
  apply (div_le_iff₀ (mul_pos hZp hZ)).2
  have he : A' * Z - Z' * A = (A' - A) * Z + A * (Z - Z') := by ring
  rw [he]
  have h₁ : |(A' - A) * Z + A * (Z - Z')| ≤ v * Z + (M * Z) * u := by
    calc
      _ ≤ |(A' - A) * Z| + |A * (Z - Z')| := abs_add_le _ _
      _ = |A' - A| * Z + |A| * |Z' - Z| := by rw [abs_mul, abs_mul, abs_of_pos hZ, abs_sub_comm Z Z']
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hNum hZ.le)
        (mul_le_mul hA hMass (abs_nonneg _) (mul_nonneg hM hZ.le))
  have h₂ := mul_le_mul_of_nonneg_right hZ' (mul_nonneg (by positivity : 0 ≤ v + M * u) hZ.le)
  nlinarith

theorem grid_nodes {R h : ℝ} {n i : ℕ} (hh : 0 ≤ h) (hn : (n : ℝ) * h = 2 * R) (hi : i < n) :
    -R ≤ -R + (i : ℝ) * h ∧ -R + ((i : ℝ) + 1) * h ≤ R := by
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hi1 : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hi
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right hi1 hh]

theorem normalizer_grid_error {R h d : ℝ} {n : ℕ} (w : ℕ → ℝ)
    (hh : 0 ≤ h) (hn : (n : ℝ) * h = 2 * R)
    (hw : ∀ i < n, |w i - weight (-R + (i : ℝ) * h)| ≤ d) :
    |h * (∑ i ∈ Finset.range n, w i) - ∫ x in (-R)..R, weight x| ≤ 2 * R * (h + d) := by
  have hm : ∀ i < n, ∀ x ∈ Set.Ioc (-R + (i : ℝ) * h) (-R + ((i : ℝ) + 1) * h),
      |weight x - weight (-R + (i : ℝ) * h)| ≤ 1 * h := by
    intro i hi x hx
    have hl := weight_lipschitz.dist_le_mul x (-R + (i : ℝ) * h)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hl
    have hd : |x - (-R + (i : ℝ) * h)| ≤ h := by
      rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - (-R + (i : ℝ) * h))]
      linarith [hx.2]
    exact hl.trans (by simpa using hd)
  have he := LocalTM2.rectangleRule_numeric_error weight w (-R) h 1 d n hh
    (fun i _ => weight_continuous.intervalIntegrable _ _) hm hw
  have hend : -R + (n : ℝ) * h = R := by linarith
  rw [hend] at he
  calc
    _ ≤ (n : ℝ) * (1 * h ^ 2 + h * d) := he
    _ = ((n : ℝ) * h) * (h + d) := by ring
    _ = _ := by rw [hn]

theorem numerator_grid_error {R h d L : ℝ} {n : ℕ} (f : ℝ → ℝ) (w : ℕ → ℝ)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hn : (n : ℝ) * h = 2 * R) (hf : LipschitzWith ⟨L,hL⟩ f) (hf0 : f 0 = 0)
    (hw : ∀ i < n, |w i - weight (-R + (i : ℝ) * h)| ≤ d) :
    |h * (∑ i ∈ Finset.range n, w i * f (-R + (i : ℝ) * h)) -
        ∫ x in (-R)..R, f x * weight x| ≤ 2 * R * L * ((1 + R) * h + R * d) := by
  have hf' : ∀ x y, |f x - f y| ≤ L * |x - y| := by
    intro x y
    have hh := hf.dist_le_mul x y
    change |f x - f y| ≤ L * |x - y| at hh
    exact hh
  have hm : ∀ i < n, ∀ x ∈ Set.Ioc (-R + (i : ℝ) * h) (-R + ((i : ℝ) + 1) * h),
      |f x * weight x - f (-R + (i : ℝ) * h) * weight (-R + (i : ℝ) * h)| ≤
        (L * (1 + R)) * h := by
    intro i hi x hx
    have hb := grid_nodes hh hn hi
    have hnode : -R + (i : ℝ) * h ∈ Set.Icc (-R) R := ⟨hb.1, by linarith⟩
    have hxp : x ∈ Set.Icc (-R) R := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hp := product_modulus hL hR hf' hf0 x (-R + (i : ℝ) * h) hxp hnode
    have hdx : |x - (-R + (i : ℝ) * h)| ≤ h := by
      rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - (-R + (i : ℝ) * h))]
      linarith [hx.2]
    exact hp.trans (mul_le_mul_of_nonneg_left hdx (by positivity))
  have hval : ∀ i < n, |w i * f (-R + (i : ℝ) * h) -
      f (-R + (i : ℝ) * h) * weight (-R + (i : ℝ) * h)| ≤ d * (L * R) := by
    intro i hi
    have hb := grid_nodes hh hn hi
    have hnode : -R + (i : ℝ) * h ∈ Set.Icc (-R) R := ⟨hb.1, by linarith⟩
    have hbound := centered_bound hL hf' hf0 _ hnode
    rw [show w i * f (-R + (i : ℝ) * h) - f (-R + (i : ℝ) * h) * weight (-R + (i : ℝ) * h) =
      (w i - weight (-R + (i : ℝ) * h)) * f (-R + (i : ℝ) * h) by ring, abs_mul]
    exact mul_le_mul (hw i hi) hbound (abs_nonneg _) hd
  have he := LocalTM2.rectangleRule_numeric_error (fun x => f x * weight x)
    (fun i => w i * f (-R + (i : ℝ) * h)) (-R) h (L * (1 + R)) (d * (L * R)) n hh
    (fun i _ => (hf.continuous.mul weight_continuous).intervalIntegrable _ _) hm hval
  have hend : -R + (n : ℝ) * h = R := by linarith
  rw [hend] at he
  calc
    _ ≤ (n : ℝ) * (L * (1 + R) * h ^ 2 + h * (d * (L * R))) := he
    _ = ((n : ℝ) * h) * L * ((1 + R) * h + R * d) := by ring
    _ = _ := by rw [hn]

theorem numerator_bound {R L : ℝ} (f : ℝ → ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hf : LipschitzWith ⟨L,hL⟩ f) (hf0 : f 0 = 0) :
    |∫ x in (-R)..R, f x * weight x| ≤ L * R * ∫ x in (-R)..R, weight x := by
  have hbound : ∀ x ∈ Set.Icc (-R) R, |f x| ≤ L * R := by
    intro x hx
    apply centered_bound hL _ hf0 x hx
    intro x y
    have hh := hf.dist_le_mul x y
    change |f x - f y| ≤ L * |x - y| at hh
    exact hh
  have hi : IntervalIntegrable (fun x => f x * weight x) volume (-R) R :=
    (hf.continuous.mul weight_continuous).intervalIntegrable (-R) R
  have hlo := intervalIntegral.integral_mono_on (μ := volume) (a := -R) (b := R)
    (f := fun x => -(L * R) * weight x) (g := fun x => f x * weight x) (by linarith)
    ((weight_continuous.const_mul _).intervalIntegrable _ _) hi (fun x hx =>
      mul_le_mul_of_nonneg_right ((abs_le.mp (hbound x hx)).1) (weight_pos x).le)
  have hhi := intervalIntegral.integral_mono_on (μ := volume) (a := -R) (b := R)
    (f := fun x => f x * weight x) (g := fun x => (L * R) * weight x) (by linarith)
    hi ((weight_continuous.const_mul _).intervalIntegrable _ _) (fun x hx =>
      mul_le_mul_of_nonneg_right ((abs_le.mp (hbound x hx)).2) (weight_pos x).le)
  rw [intervalIntegral.integral_const_mul] at hlo hhi
  rw [abs_le]
  constructor <;> linarith

theorem normalized_grid_error {R h d L : ℝ} {n : ℕ} (f : ℝ → ℝ) (w : ℕ → ℝ)
    (hL : 0 ≤ L) (hR : 1 ≤ R) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hn : (n : ℝ) * h = 2 * R) (hf : LipschitzWith ⟨L,hL⟩ f) (hf0 : f 0 = 0)
    (hw : ∀ i < n, |w i - weight (-R + (i : ℝ) * h)| ≤ d)
    (hsmall : 2 * R * (h + d) ≤ 1 / 2) :
    |(h * ∑ i ∈ Finset.range n, w i * f (-R + (i : ℝ) * h)) /
        (h * ∑ i ∈ Finset.range n, w i) -
        (∫ x in (-R)..R, f x * weight x) / (∫ x in (-R)..R, weight x)| ≤
      6 * L * R ^ 2 * (h + d) := by
  have hZ := normalizer_lower hR
  have hZerr := normalizer_grid_error w hh hn hw
  have hZtilde : 1 ≤ h * ∑ i ∈ Finset.range n, w i := by
    have hh := (abs_le.mp hZerr).1
    linarith
  have hZpos : 0 < ∫ x in (-R)..R, weight x := by linarith
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hA := numerator_bound f hL hR0 hf hf0
  have hAerr := numerator_grid_error f w hL hR0 hh hd hn hf hf0 hw
  have herr := ratio_error hZpos hZtilde (mul_nonneg hL hR0)
    (by positivity : 0 ≤ 2 * R * (h + d))
    (by positivity : 0 ≤ 2 * R * L * ((1 + R) * h + R * d)) hZerr hA hAerr
  apply herr.trans
  have hb : h ≤ R * (h + d) := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * L * R)
  nlinarith

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

theorem gaussianMesh_le_one (k : ℕ) : gaussianMesh k ≤ 1 := by
  dsimp [gaussianMesh]
  have hd : (1 : ℚ) ≤ gaussianMeshDen k := by
    exact_mod_cast (gaussianMeshDen_positive k)
  exact (div_le_one (by positivity)).mpr hd

theorem gaussian_grid_interval (k : ℕ) :
    (gaussianGridSize k : ℝ) * (gaussianMesh k : ℝ) = 2 * (gaussianRadius k : ℝ) := by
  simp [gaussianGridSize, gaussianMesh, (Nat.ne_of_gt (gaussianMeshDen_positive k))]

theorem gaussianNodes_correct (k : ℕ) (fuel : List Bool) (hf : gaussianGridSize k ≤ fuel.length) :
    gaussianNodes (k, fuel) = List.ofFn (fun i : Fin (gaussianGridSize k) => gaussianNode (k, i.val)) := by
  simp only [gaussianNodes, boolIndices, List.length_take, Nat.min_eq_left hf]
  exact map_range_eq_ofFn _ _

theorem gaussian_uniform_fuel (k : ℕ) (fuel : List Bool) (hf : gaussianCoinBudget k ≤ fuel.length) :
    2 / (gaussianMesh k : ℝ) ^ 3 + 2 ≤ (unitize fuel).length := by
  have hden : (gaussianMeshDen k : ℝ) ≠ 0 := by exact_mod_cast (gaussianMeshDen_positive k).ne'
  have heq : 2 / (gaussianMesh k : ℝ) ^ 3 + 2 = 2 * (gaussianMeshDen k : ℝ) ^ 3 + 2 := by
    simp only [gaussianMesh, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    field_simp
  rw [heq]
  have hh : 2 * (gaussianMeshDen k) ^ 3 + 2 ≤ fuel.length := by
    dsimp only [gaussianCoinBudget] at hf
    omega
  simpa only [unitize, List.length_map] using (show (2 : ℝ) * (gaussianMeshDen k : ℝ) ^ 3 + 2 ≤ fuel.length by exact_mod_cast hh)

theorem gaussianWeights_correct (k : ℕ) (fuel : List Bool) (hf : gaussianCoinBudget k ≤ fuel.length) :
    gaussianWeights (k, fuel) = List.ofFn (fun i : Fin (gaussianGridSize k) =>
      expNegativeApprox ((gaussianNode (k, i.val)) ^ 2 / 4) (gaussianMesh k)) := by
  have hgrid : gaussianGridSize k ≤ fuel.length := by dsimp only [gaussianCoinBudget] at hf; omega
  rw [gaussianWeights, gaussianNodes_correct k fuel hgrid, List.map_ofFn]
  congr 1
  funext i
  change expWithFuel ((gaussianNode (k, i.val) * gaussianNode (k, i.val) / 4, gaussianMesh k),
    unitize fuel) = _
  rw [show gaussianNode (k, i.val) * gaussianNode (k, i.val) / 4 = (gaussianNode (k, i.val)) ^ 2 / 4 by ring]
  exact expWithFuel_eq_uniform _ _ (by positivity) (gaussianMesh_positive k) _ (gaussian_uniform_fuel k fuel hf)

theorem gaussianWeight_accuracy (k : ℕ) (i : Fin (gaussianGridSize k)) :
    0 ≤ expNegativeApprox ((gaussianNode (k, i.val)) ^ 2 / 4) (gaussianMesh k) ∧
      |(expNegativeApprox ((gaussianNode (k, i.val)) ^ 2 / 4) (gaussianMesh k) : ℝ) -
        CritWinSpin.Implementation.GaussianGrid.weight
          (-(gaussianRadius k : ℝ) + (i.val : ℝ) * (gaussianMesh k : ℝ))| ≤ (gaussianMesh k : ℝ) := by
  have hh := expNegativeApprox_error ((gaussianNode (k, i.val)) ^ 2 / 4) (gaussianMesh k)
    (by positivity) (gaussianMesh_positive k) (gaussianMesh_le_one k)
  refine ⟨hh.1, ?_⟩
  convert hh.2 using 1
  simp only [CritWinSpin.Implementation.GaussianGrid.weight, gaussianNode, Rat.cast_div,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_add, Rat.cast_neg, Rat.cast_mul, Rat.cast_natCast]
  ring

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

theorem take_ofFn_prefix (L R : ℕ) (ω : Fin (L + R) → Bool) :
    (List.ofFn ω).take L = List.ofFn (fun i => ω (Fin.castAdd R i)) := by
  rw [← Fin.ofFn_take_eq_take_ofFn (Nat.le_add_right L R)]
  rfl

theorem scalarTable_expectation {n : ℕ} (v : Fin n → ℚ) (L R : ℕ)
    (cs : Fin n → ℕ) (htotal : ∑ i, cs i = 2 ^ L) (f : ℚ → ℝ) :
    (1 / (2 : ℝ) ^ (L + R)) *
        (∑ ω : Fin (L + R) → Bool,
          f (sampleScalarTable ((List.ofFn v, List.ofFn cs), (List.ofFn ω).take L))) =
      ∑ i, f (v i) * ((cs i : ℝ) / (2 : ℝ) ^ L) := by
  have he (ω : Fin (L + R) → Bool) :
      sampleScalarTable ((List.ofFn v, List.ofFn cs), (List.ofFn ω).take L) =
        v (FiniteTicket.drawIndex L cs htotal (fun i => ω (Fin.castAdd R i))) := by
    rw [take_ofFn_prefix]
    exact sampleScalarTable_ofFn v L cs htotal _
  simp_rw [he]
  exact (FiniteTicket.unused_bits_expectation L R
    (fun ω => f (v (FiniteTicket.drawIndex L cs htotal ω)))).trans
    (drawIndex_expectation L cs htotal (fun i => f (v i)))

theorem quantized_mean_error {n : ℕ} (hn : 0 < n) (v : Fin n → ℚ)
    (p : Fin n → ℝ) (hp : IsDistribution p) (bits : ℕ)
    (L R : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hv : ∀ i, |(v i : ℝ)| ≤ R) (f : ℝ → ℝ) (hf : LipschitzWith ⟨L, hL⟩ f) :
    |(∑ i, f (v i) *
        ((DyadicRounding.counts p (2 ^ bits) ⟨0, hn⟩ i : ℝ) / (2 : ℝ) ^ bits)) -
      ∑ i, f (v i) * p i| ≤ 2 * L * R * (n : ℝ) / (2 : ℝ) ^ bits := by
  classical
  let q : Fin n → ℝ := fun i =>
    (DyadicRounding.counts p (2 ^ bits) ⟨0, hn⟩ i : ℝ) / (2 : ℝ) ^ bits
  have hq : IsDistribution q := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      DyadicRounding.law_distribution p hp (2 ^ bits) (by positivity) ⟨0, hn⟩
  have ht : tvDist q p ≤ (n : ℝ) / (2 : ℝ) ^ bits := by
    simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
      DyadicRounding.tv_error p hp (2 ^ bits) (by positivity) ⟨0, hn⟩
  let g : Fin n → ℝ := fun i => f (v i) - f 0
  have hg : ∀ i, |g i| ≤ L * R := by
    intro i
    have hh := hf.dist_le_mul (v i) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hv i) hL)
  have hmean := bounded_mean_tv g q p (L * R) hg
  have hc : (∑ i, g i * q i) - ∑ i, g i * p i =
      (∑ i, f (v i) * q i) - ∑ i, f (v i) * p i := by
    simp only [g, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2, hq.2, mul_one]
    ring
  rw [hc] at hmean
  apply hmean.trans
  have hh := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * (L * R))
  convert hh using 1 <;> ring

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CritWinSpin.Implementation.GaussianGridLaw

open GaussianGrid

def normalizingConstant : ℝ := (Real.sqrt (2 * Real.pi * 2))⁻¹

theorem normalizingConstant_pos : 0 < normalizingConstant := by
  dsimp [normalizingConstant]
  positivity

theorem pdf_eq (x : ℝ) : gaussianPDFReal 0 2 x = normalizingConstant * weight x := by
  dsimp [gaussianPDFReal, normalizingConstant, weight]
  change (Real.sqrt (2 * Real.pi * 2))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * 2)) = _
  rw [sub_zero, show (2 : ℝ) * 2 = 4 by norm_num]

theorem truncated_integral (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in LocalTM2.truncationSet R, f x ∂gaussianReal 0 2) =
      normalizingConstant * ∫ x in (-R)..R, f x * weight x := by
  unfold LocalTM2.truncationSet
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  change (∫ x in Set.Icc (-R) R, f x ∂(volume : Measure ℝ).withDensity (fun x => gaussianPDF 0 2 x)) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_gaussianPDF 0 2)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f measurableSet_Icc]
  have hDen : ∀ x : ℝ, (gaussianPDF 0 2 x).toReal = normalizingConstant * weight x := by
    intro x
    rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 2 x), pdf_eq]
  simp only [smul_eq_mul, hDen]
  have he : (fun x : ℝ => normalizingConstant * weight x * f x) =
      fun x => normalizingConstant * (f x * weight x) := by funext x; ring
  rw [he, integral_const_mul]
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith : -R ≤ R)]

theorem truncated_mass {R : ℝ} (hR : 0 ≤ R) :
    (gaussianReal 0 2).real (LocalTM2.truncationSet R) =
      normalizingConstant * ∫ x in (-R)..R, weight x := by
  have hh := truncated_integral (fun _ : ℝ => (1 : ℝ)) hR
  simpa only [setIntegral_const, smul_eq_mul, one_smul, mul_one, one_mul] using hh

theorem truncated_mass_pos {R : ℝ} (hR : 1 ≤ R) :
    0 < (gaussianReal 0 2).real (LocalTM2.truncationSet R) := by
  rw [truncated_mass (le_trans zero_le_one hR)]
  exact mul_pos normalizingConstant_pos (lt_of_lt_of_le (by norm_num) (normalizer_lower hR))

theorem conditional_mean (f : ℝ → ℝ) {R : ℝ} (hR : 1 ≤ R) :
    (∫ x in LocalTM2.truncationSet R, f x ∂gaussianReal 0 2) /
        (gaussianReal 0 2).real (LocalTM2.truncationSet R) =
      (∫ x in (-R)..R, f x * weight x) / (∫ x in (-R)..R, weight x) := by
  rw [truncated_integral f (le_trans zero_le_one hR), truncated_mass (le_trans zero_le_one hR),
    mul_div_mul_left _ _ normalizingConstant_pos.ne']

theorem centered_integrable {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : LipschitzWith ⟨L,hL⟩ f) (hf0 : f 0 = 0) : Integrable f (gaussianReal 0 2) := by
  have hi : Integrable (fun x : ℝ => |x|) (gaussianReal 0 2) := by
    simpa only [Real.norm_eq_abs, id_eq] using
      (IsGaussian.integrable_id (μ := gaussianReal 0 2)).norm
  refine (hi.const_mul L).mono' hf.continuous.measurable.aestronglyMeasurable ?_
  filter_upwards with x
  have hh := hf.dist_le_mul x 0
  change |f x - f 0| ≤ L * |x - 0| at hh
  simpa only [Real.norm_eq_abs, hf0, sub_zero] using hh

theorem centered_grid_mean_error {R h d L : ℝ} {n : ℕ} (f : ℝ → ℝ) (w : ℕ → ℝ)
    (hL : 0 ≤ L) (hR : 1 ≤ R) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hn : (n : ℝ) * h = 2 * R) (hf : LipschitzWith ⟨L,hL⟩ f) (hf0 : f 0 = 0)
    (hw : ∀ i < n, |w i - weight (-R + (i : ℝ) * h)| ≤ d)
    (hsmall : 2 * R * (h + d) ≤ 1 / 2) :
    |(∫ x : ℝ, f x ∂gaussianReal 0 2) -
        (h * ∑ i ∈ Finset.range n, w i * f (-R + (i : ℝ) * h)) /
          (h * ∑ i ∈ Finset.range n, w i)| ≤ L * (4 / R + 6 * R ^ 2 * (h + d)) := by
  have hfI := centered_integrable hL hf hf0
  have hp : ∀ x : ℝ, |f x| ≤ L * |x| := by
    intro x
    have ht := hf.dist_le_mul x 0
    change |f x - f 0| ≤ L * |x - 0| at ht
    simpa only [hf0, sub_zero] using ht
  have ht := LocalTM2.truncated_mean_error (gaussianReal 0 2) f hfI L R 2 hL
    (lt_of_lt_of_le zero_lt_one hR) LocalTM2.gaussianTwo_sq_integrable
    LocalTM2.gaussianTwo_second_moment.le hp (truncated_mass_pos hR)
  rw [conditional_mean f hR] at ht
  have hg := normalized_grid_error f w hL hR hh hd hn hf hf0 hw hsmall
  rw [abs_sub_comm] at hg
  have htri := abs_sub_le (∫ x : ℝ, f x ∂gaussianReal 0 2)
    ((∫ x in (-R)..R, f x * weight x) / (∫ x in (-R)..R, weight x))
    ((h * ∑ i ∈ Finset.range n, w i * f (-R + (i : ℝ) * h)) / (h * ∑ i ∈ Finset.range n, w i))
  have he : 2 * L * 2 / R = L * (4 / R) := by ring
  rw [he] at ht
  nlinarith

theorem grid_mean_error {R h d L : ℝ} {n : ℕ} (f : ℝ → ℝ) (w : ℕ → ℝ)
    (hL : 0 ≤ L) (hR : 1 ≤ R) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hn : (n : ℝ) * h = 2 * R) (hf : LipschitzWith ⟨L,hL⟩ f)
    (hw : ∀ i < n, |w i - weight (-R + (i : ℝ) * h)| ≤ d)
    (hsmall : 2 * R * (h + d) ≤ 1 / 2) :
    |(∫ x : ℝ, f x ∂gaussianReal 0 2) -
        (h * ∑ i ∈ Finset.range n, w i * f (-R + (i : ℝ) * h)) /
          (h * ∑ i ∈ Finset.range n, w i)| ≤ L * (4 / R + 6 * R ^ 2 * (h + d)) := by
  let g : ℝ → ℝ := fun x => f x - f 0
  have hg : LipschitzWith ⟨L,hL⟩ g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have ht := hf.dist_le_mul x y
    change |f x - f y| ≤ L * |x - y| at ht
    change |(f x - f 0) - (f y - f 0)| ≤ L * |x - y|
    rw [show (f x - f 0) - (f y - f 0) = f x - f y by ring]
    exact ht
  have hg0 : g 0 = 0 := sub_self _
  have hig := centered_integrable hL hg hg0
  have hif : Integrable f (gaussianReal 0 2) := by
    have he : f = fun x => g x + f 0 := by funext x; dsimp [g]; ring
    rw [he]
    exact hig.add (integrable_const (f 0))
  have hInt : (∫ x, g x ∂gaussianReal 0 2) = (∫ x, f x ∂gaussianReal 0 2) - f 0 := by
    change (∫ x, f x - f 0 ∂gaussianReal 0 2) = _
    rw [integral_sub hif (integrable_const _), integral_const, probReal_univ, one_smul]
  have hz := normalizer_lower hR
  have hze := normalizer_grid_error w hh hn hw
  have hz' : 1 ≤ h * ∑ i ∈ Finset.range n, w i := by
    have hlow := (abs_le.mp hze).1
    linarith
  have hzn : h * (∑ i ∈ Finset.range n, w i) ≠ 0 := by linarith
  have hNum : (h * ∑ i ∈ Finset.range n, w i * g (-R + (i : ℝ) * h)) /
      (h * ∑ i ∈ Finset.range n, w i) =
      (h * ∑ i ∈ Finset.range n, w i * f (-R + (i : ℝ) * h)) /
        (h * ∑ i ∈ Finset.range n, w i) - f 0 := by
    have he : (∑ i ∈ Finset.range n, w i * g (-R + (i : ℝ) * h)) =
        (∑ i ∈ Finset.range n, w i * f (-R + (i : ℝ) * h)) - f 0 * (∑ i ∈ Finset.range n, w i) := by
      dsimp [g]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    rw [he]
    have hhn := (mul_ne_zero_iff.mp hzn).1
    have hwn := (mul_ne_zero_iff.mp hzn).2
    field_simp [hhn, hwn] <;> ring
  have hc := centered_grid_mean_error g w hL hR hh hd hn hg hg0 hw hsmall
  rw [hInt, hNum] at hc
  have hcancel (u v c : ℝ) : (u - c) - (v - c) = u - v := by ring
  rw [hcancel] at hc
  exact hc

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

def nominalGaussianWeight (k i : ℕ) : ℚ :=
  expNegativeApprox ((gaussianNode (k, i)) ^ 2 / 4) (gaussianMesh k)

theorem gaussianGridSize_positive (k : ℕ) : 0 < gaussianGridSize k := by
  have := gaussianMeshDen_positive k
  dsimp [gaussianGridSize, gaussianRadius]
  positivity

theorem gaussianDraw_table (k tail : ℕ)
    (hb : gaussianCoinBudget k ≤ gaussianBits k + tail)
    (ω : Fin (gaussianBits k + tail) → Bool) :
    gaussianDraw (k, List.ofFn ω) =
      sampleScalarTable
        ((List.ofFn (fun i : Fin (gaussianGridSize k) => gaussianNode (k, i.val)),
          quantizedCounts
            (List.ofFn (fun i : Fin (gaussianGridSize k) => nominalGaussianWeight k i.val),
              2 ^ gaussianBits k)), (List.ofFn ω).take (gaussianBits k)) := by
  have hf : gaussianCoinBudget k ≤ (List.ofFn ω).length := by simpa using hb
  have hn : gaussianGridSize k ≤ (List.ofFn ω).length := by
    dsimp only [gaussianCoinBudget] at hf
    omega
  unfold gaussianDraw gaussianCounts sampleScalarTable
  rw [gaussianWeights_correct k (List.ofFn ω) hf, gaussianNodes_correct k (List.ofFn ω) hn]
  rfl

theorem gaussianDraw_expectation (k tail : ℕ)
    (hb : gaussianCoinBudget k ≤ gaussianBits k + tail)
    (hW : 0 < ∑ i : Fin (gaussianGridSize k), nominalGaussianWeight k i.val)
    (f : ℝ → ℝ) :
    (1 / (2 : ℝ) ^ (gaussianBits k + tail)) *
        (∑ ω : Fin (gaussianBits k + tail) → Bool, f (gaussianDraw (k, List.ofFn ω))) =
      ∑ i : Fin (gaussianGridSize k), f (gaussianNode (k, i.val)) *
        ((DyadicRounding.counts
          (fun i : Fin (gaussianGridSize k) =>
            (nominalGaussianWeight k i.val : ℝ) /
              ∑ j : Fin (gaussianGridSize k), (nominalGaussianWeight k j.val : ℝ))
          (2 ^ gaussianBits k) ⟨0, gaussianGridSize_positive k⟩ i : ℝ) /
            (2 : ℝ) ^ gaussianBits k) := by
  classical
  let w : Fin (gaussianGridSize k) → ℚ := fun i => nominalGaussianWeight k i.val
  let p : Fin (gaussianGridSize k) → ℝ := fun i => (w i : ℝ) / ∑ j, (w j : ℝ)
  have hp : IsDistribution p := by
    have hWr : (0 : ℝ) < ∑ i, (w i : ℝ) := by exact_mod_cast hW
    refine ⟨fun i => div_nonneg (by
      exact_mod_cast (gaussianWeight_accuracy k i).1) hWr.le, ?_⟩
    rw [← Finset.sum_div]
    exact div_self hWr.ne'
  let cs := DyadicRounding.counts p (2 ^ gaussianBits k) ⟨0, gaussianGridSize_positive k⟩
  have htotal : ∑ i, cs i = 2 ^ gaussianBits k := DyadicRounding.counts_total p hp _ _
  have he (ω : Fin (gaussianBits k + tail) → Bool) :
      gaussianDraw (k, List.ofFn ω) =
        sampleScalarTable ((List.ofFn (fun i : Fin (gaussianGridSize k) =>
          gaussianNode (k, i.val)), List.ofFn cs), (List.ofFn ω).take (gaussianBits k)) := by
    rw [gaussianDraw_table k tail hb ω, quantizedCounts_ofFn_pos (gaussianGridSize_positive k)]
  simp_rw [he]
  exact scalarTable_expectation _ _ _ cs htotal (fun x : ℚ => f (x : ℝ))

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

theorem gaussianGrid_sum_positive (k : ℕ)
    (hsmall : 2 * (gaussianRadius k : ℝ) *
      ((gaussianMesh k : ℝ) + (gaussianMesh k : ℝ)) ≤ 1 / 2) :
    0 < ∑ i : Fin (gaussianGridSize k), nominalGaussianWeight k i.val := by
  have hR : 1 ≤ (gaussianRadius k : ℝ) := by
    have hh : 1 ≤ gaussianRadius k := by unfold gaussianRadius; omega
    exact_mod_cast hh
  let w : ℕ → ℝ := fun i => nominalGaussianWeight k i
  have hw : ∀ i < gaussianGridSize k,
      |w i - weight (-(gaussianRadius k : ℝ) + i * (gaussianMesh k : ℝ))| ≤ (gaussianMesh k : ℝ) := by
    intro i hi
    exact (gaussianWeight_accuracy k ⟨i, hi⟩).2
  have hz := normalizer_lower hR
  have he := normalizer_grid_error w
    (show 0 ≤ (gaussianMesh k : ℝ) from by exact_mod_cast (gaussianMesh_positive k).le)
    (gaussian_grid_interval k) hw
  have he' := (abs_le.mp he).1
  have hs : 1 ≤ (gaussianMesh k : ℝ) * ∑ i ∈ Finset.range (gaussianGridSize k), w i := by
    linarith
  have hp : 0 < ∑ i ∈ Finset.range (gaussianGridSize k), w i := by
    have hd : 0 < (gaussianMesh k : ℝ) := by exact_mod_cast gaussianMesh_positive k
    nlinarith
  rw [← Fin.sum_univ_eq_sum_range] at hp
  dsimp only [w] at hp
  exact_mod_cast hp

theorem gaussianDraw_weak_error (k tail : ℕ)
    (hb : gaussianCoinBudget k ≤ gaussianBits k + tail)
    (hsmall : 2 * (gaussianRadius k : ℝ) *
      ((gaussianMesh k : ℝ) + (gaussianMesh k : ℝ)) ≤ 1 / 2)
    (L : ℝ) (hL : 0 ≤ L) (f : ℝ → ℝ) (hf : LipschitzWith ⟨L, hL⟩ f) :
    |(1 / (2 : ℝ) ^ (gaussianBits k + tail)) *
        (∑ ω : Fin (gaussianBits k + tail) → Bool, f (gaussianDraw (k, List.ofFn ω))) -
      (∫ x : ℝ, f x ∂gaussianReal 0 2)| ≤
        L * (4 / (gaussianRadius k : ℝ) +
          6 * (gaussianRadius k : ℝ) ^ 2 *
            ((gaussianMesh k : ℝ) + (gaussianMesh k : ℝ))) +
          2 * L * (gaussianRadius k : ℝ) * (gaussianGridSize k : ℝ) /
            (2 : ℝ) ^ gaussianBits k := by
  classical
  let n := gaussianGridSize k
  let w : ℕ → ℝ := fun i => nominalGaussianWeight k i
  let v : Fin n → ℚ := fun i => gaussianNode (k, i.val)
  let p : Fin n → ℝ := fun i => w i.val / ∑ j : Fin n, w j.val
  have hn : 0 < n := gaussianGridSize_positive k
  have hW := gaussianGrid_sum_positive k hsmall
  have hWr : (0 : ℝ) < ∑ i : Fin n, w i.val := by
    dsimp only [w, n]
    exact_mod_cast hW
  have hp : IsDistribution p := by
    refine ⟨fun i => div_nonneg (by
      change (0 : ℝ) ≤ (nominalGaussianWeight k i.val : ℝ)
      exact_mod_cast (gaussianWeight_accuracy k i).1) hWr.le, ?_⟩
    rw [← Finset.sum_div]
    exact div_self hWr.ne'
  have hE := gaussianDraw_expectation k tail hb hW f
  rw [hE]
  have ht := quantized_mean_error hn v p hp (gaussianBits k) L (gaussianRadius k)
    hL (by positivity) (gaussianNode_bound k) f hf
  have hR : 1 ≤ (gaussianRadius k : ℝ) := by
    have hh : 1 ≤ gaussianRadius k := by unfold gaussianRadius; omega
    exact_mod_cast hh
  have hd : 0 < (gaussianMesh k : ℝ) := by exact_mod_cast gaussianMesh_positive k
  have hw : ∀ i < n, |w i - weight (-(gaussianRadius k : ℝ) +
      i * (gaussianMesh k : ℝ))| ≤ (gaussianMesh k : ℝ) := by
    intro i hi
    exact (gaussianWeight_accuracy k ⟨i, hi⟩).2
  have hg := CritWinSpin.Implementation.GaussianGridLaw.grid_mean_error f w hL hR
    hd.le hd.le (gaussian_grid_interval k) hf hw hsmall
  have hsum : (∑ i : Fin n, w i.val) = ∑ i ∈ Finset.range n, w i :=
    Fin.sum_univ_eq_sum_range _ n
  have hnum : (∑ i : Fin n, f (v i) * w i.val) =
      ∑ i ∈ Finset.range n, w i * f (-(gaussianRadius k : ℝ) +
        i * (gaussianMesh k : ℝ)) := by
    calc
      _ = ∑ i ∈ Finset.range n, f (gaussianNode (k, i)) * w i :=
        Fin.sum_univ_eq_sum_range (fun i => f (gaussianNode (k, i)) * w i) n
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [gaussianNode, Rat.cast_add, Rat.cast_neg, Rat.cast_natCast, Rat.cast_mul]
        ring
  have hm : (∑ i : Fin n, f (v i) * p i) =
      ((gaussianMesh k : ℝ) * ∑ i ∈ Finset.range n, w i *
        f (-(gaussianRadius k : ℝ) + i * (gaussianMesh k : ℝ))) /
        ((gaussianMesh k : ℝ) * ∑ i ∈ Finset.range n, w i) := by
    change (∑ i : Fin n, f (v i) * (w i.val / ∑ j : Fin n, w j.val)) = _
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, hnum, hsum]
    exact (mul_div_mul_left _ _ hd.ne').symm
  rw [← hm] at hg
  have hgrev := hg
  rw [abs_sub_comm] at hgrev
  exact (abs_sub_le _ (∑ i : Fin n, f (v i) * p i) _).trans
    ((add_le_add ht hgrev).trans_eq (by ring))

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled

theorem gaussian_parameter_formulas (k : ℕ) :
    (gaussianRadius k : ℝ) = 16 * ((k : ℝ) + 1) ∧
      (gaussianMesh k : ℝ) = 1 / (16384 * ((k : ℝ) + 1) ^ 4) ∧
      (gaussianAccuracy k : ℝ) = 64 * (16 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) := by
  simp [gaussianRadius, gaussianMesh, gaussianMeshDen, gaussianAccuracy]

theorem gaussian_schedule_small (k : ℕ) :
    2 * (gaussianRadius k : ℝ) *
      ((gaussianMesh k : ℝ) + (gaussianMesh k : ℝ)) ≤ 1 / 2 := by
  obtain ⟨hr, hd, _⟩ := gaussian_parameter_formulas k
  rw [hr, hd]
  let z : ℝ := k + 1
  have hz : 1 ≤ z := by dsimp [z]; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hz0 : 0 < z := by linarith
  have hz2 : z ≤ z ^ 2 := by nlinarith [sq_nonneg (z - 1)]
  have hz2' : 1 ≤ z ^ 2 := by linarith
  have hz4 : z ≤ z ^ 4 := by nlinarith [sq_nonneg (z ^ 2 - 1)]
  change 2 * (16 * z) * (1 / (16384 * z ^ 4) + 1 / (16384 * z ^ 4)) ≤ 1 / 2
  have he : 2 * (16 * z) * (1 / (16384 * z ^ 4) + 1 / (16384 * z ^ 4)) =
      (64 * z) / (16384 * z ^ 4) := by ring
  rw [he, div_le_iff₀ (by positivity : 0 < 16384 * z ^ 4)]
  nlinarith

theorem gaussian_error_schedule (k : ℕ) :
    4 / (gaussianRadius k : ℝ) +
      6 * (gaussianRadius k : ℝ) ^ 2 *
        ((gaussianMesh k : ℝ) + (gaussianMesh k : ℝ)) +
      (gaussianRadius k : ℝ) / (2 * (gaussianAccuracy k : ℝ)) ≤ 1 / ((k : ℝ) + 1) := by
  obtain ⟨hr, hd, hm⟩ := gaussian_parameter_formulas k
  rw [hr, hd, hm]
  let z : ℝ := k + 1
  have hz : 1 ≤ z := by dsimp [z]; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hz0 : 0 < z := by linarith
  have hz2 : z ≤ z ^ 2 := by nlinarith [sq_nonneg (z - 1)]
  change 4 / (16 * z) + 6 * (16 * z) ^ 2 *
      (1 / (16384 * z ^ 4) + 1 / (16384 * z ^ 4)) +
      (16 * z) / (2 * (64 * (16 * z) * z)) ≤ 1 / z
  have he : 4 / (16 * z) + 6 * (16 * z) ^ 2 *
      (1 / (16384 * z ^ 4) + 1 / (16384 * z ^ 4)) +
      (16 * z) / (2 * (64 * (16 * z) * z)) =
        1 / (4 * z) + 3 / (16 * z ^ 2) + 1 / (128 * z) := by
    field_simp
    <;> ring
  rw [he]
  have hf : 3 / (16 * z ^ 2) ≤ 3 / (16 * z) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  calc
    _ ≤ 1 / (4 * z) + 3 / (16 * z) + 1 / (128 * z) := by linarith
    _ ≤ 1 / z := by
      field_simp
      nlinarith

end CritWinSpin.LocalTM2.Compiled

end

section

set_option autoImplicit false

namespace CritWinSpin.LocalTM2
open MeasureTheory
noncomputable section





theorem integral_uniformBits (bits : ℕ) (f : (Fin bits → Bool) → ℝ) :
    (∫ ω, f ω ∂uniformBits bits) = (1 / (2 : ℝ) ^ bits) * ∑ ω, f ω := by
  rw [uniformBits, PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, ← Finset.mul_sum]





theorem integral_bitLaw (bits : ℕ) (draw : (Fin bits → Bool) → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂bitLaw bits draw) = (1 / (2 : ℝ) ^ bits) * ∑ ω, f (draw ω) := by
  rw [bitLaw, integral_map (measurable_of_finite draw).aemeasurable hf.aestronglyMeasurable]
  exact integral_uniformBits bits _

end
end CritWinSpin.LocalTM2

end

section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace CritWinSpin.LocalTM2.Compiled
open MeasureTheory ProbabilityTheory

theorem gaussianDraw_error_final (k tail : ℕ)
    (hb : gaussianCoinBudget k ≤ gaussianBits k + tail)
    (L : ℝ) (hL : 0 ≤ L) (f : ℝ → ℝ) (hf : LipschitzWith ⟨L, hL⟩ f) :
    |(1 / (2 : ℝ) ^ (gaussianBits k + tail)) *
        (∑ ω : Fin (gaussianBits k + tail) → Bool, f (gaussianDraw (k, List.ofFn ω))) -
      (∫ x : ℝ, f x ∂gaussianReal 0 2)| ≤ L / ((k : ℝ) + 1) := by
  have he := gaussianDraw_weak_error k tail hb (gaussian_schedule_small k) L hL f hf
  have hm : 0 < gaussianAccuracy k := by dsimp [gaussianAccuracy, gaussianRadius]; positivity
  have ht := tableRounding_error_bound (gaussianGridSize k) (gaussianAccuracy k) hm
  change (gaussianGridSize k : ℝ) / (2 : ℝ) ^ gaussianBits k ≤
    1 / (4 * (gaussianAccuracy k : ℝ)) at ht
  have htm := mul_le_mul_of_nonneg_left ht
    (by positivity : 0 ≤ 2 * L * (gaussianRadius k : ℝ))
  have ht' : 2 * L * (gaussianRadius k : ℝ) * (gaussianGridSize k : ℝ) /
      (2 : ℝ) ^ gaussianBits k ≤ L * (gaussianRadius k : ℝ) / (2 * (gaussianAccuracy k : ℝ)) := by
    calc
      _ = (2 * L * (gaussianRadius k : ℝ)) *
        ((gaussianGridSize k : ℝ) / (2 : ℝ) ^ gaussianBits k) := by ring
      _ ≤ (2 * L * (gaussianRadius k : ℝ)) * (1 / (4 * (gaussianAccuracy k : ℝ))) := htm
      _ = _ := by ring
  apply he.trans
  calc
    _ ≤ L * (4 / (gaussianRadius k : ℝ) +
      6 * (gaussianRadius k : ℝ) ^ 2 * ((gaussianMesh k : ℝ) + (gaussianMesh k : ℝ))) +
        L * (gaussianRadius k : ℝ) / (2 * (gaussianAccuracy k : ℝ)) := add_le_add le_rfl ht'
    _ = L * (4 / (gaussianRadius k : ℝ) +
      6 * (gaussianRadius k : ℝ) ^ 2 * ((gaussianMesh k : ℝ) + (gaussianMesh k : ℝ)) +
        (gaussianRadius k : ℝ) / (2 * (gaussianAccuracy k : ℝ))) := by ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (gaussian_error_schedule k) hL
      simpa only [div_eq_mul_inv, one_mul] using hh




theorem gaussianNoiseBits_budget (k : ℕ) : gaussianNoiseBits k = gaussianCoinBudget k := by
  unfold gaussianNoiseBits gaussianNoiseTail gaussianCoinBudget
  omega





theorem gaussianNoiseLaw_weak (k : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (f : ℝ → ℝ) (hf : LipschitzWith ⟨L, hL⟩ f) :
    |(∫ x, f x ∂gaussianNoiseLaw k) - (∫ x, f x ∂gaussianReal 0 2)| ≤ L / ((k : ℝ) + 1) := by
  rw [gaussianNoiseLaw, integral_bitLaw _ _ f hf.continuous.measurable]
  exact gaussianDraw_error_final k (gaussianNoiseTail k)
    (by rw [← gaussianNoiseBits_budget]; rfl) L hL f hf

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

theorem uniform_function_measure (N B : ℕ) :
    (PMF.uniformOfFintype (Fin N → Fin B → Bool)).toMeasure =
      Measure.pi (fun _ : Fin N => uniformBits B) := by
  apply Measure.ext_of_singleton
  intro ω
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _), Measure.pi_singleton]
  simp [uniformBits, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    PMF.uniformOfFintype_apply, ← pow_mul]
  rw [pow_mul, ENNReal.inv_pow]

theorem split_uniformBits (N B : ℕ) :
    (uniformBits (N * B)).map (splitBitEquiv N B) =
      (PMF.uniformOfFintype (Fin N → Fin B → Bool)).toMeasure := by
  apply Measure.ext_of_singleton
  intro ω
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton _)]
  have hp : (splitBitEquiv N B) ⁻¹' {ω} = {(splitBitEquiv N B).symm ω} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Equiv.apply_eq_iff_eq_symm_apply]
  rw [hp, uniformBits, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  simp [PMF.uniformOfFintype_apply, ← pow_mul, Nat.mul_comm]

theorem product_bitLaw (N B : ℕ) (draw : (Fin B → Bool) → ℝ) :
    (uniformBits (N * B)).map
        (fun ω => WithLp.toLp 2 (fun i : Fin N => draw (fun j => ω (blockIndex i j)))) =
      (Measure.pi (fun _ : Fin N => bitLaw B draw)).map
        (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)) := by
  have hsplit : (fun ω => WithLp.toLp 2 (fun i : Fin N => draw (fun j => ω (blockIndex i j)))) =
      (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)) ∘
        ((fun ω i => draw (ω i)) ∘ splitBitEquiv N B) := by
    funext ω
    congr 1
    funext i
    change draw (fun j => ω (blockIndex i j)) = draw (splitBitEquiv N B ω i)
    congr 1
    funext j
    exact (splitBitEquiv_apply N B ω i j).symm
  rw [hsplit, ← Measure.map_map (WithLp.measurable_toLp 2 (Fin N → ℝ))
    ((measurable_of_finite (fun ω : Fin N → Fin B → Bool => fun i => draw (ω i))).comp
      (measurable_of_finite (splitBitEquiv N B)))]
  congr 1
  rw [← Measure.map_map (measurable_of_finite (fun ω : Fin N → Fin B → Bool => fun i => draw (ω i)))
    (measurable_of_finite (splitBitEquiv N B)), split_uniformBits, uniform_function_measure]
  exact Measure.pi_map_pi (fun _ : Fin N => (measurable_of_finite draw).aemeasurable)

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

def CoordinateLip {n : ℕ} (f : (Fin n → ℝ) → ℝ) (L : ℝ) : Prop :=
  ∀ (i : Fin n) (x y : Fin n → ℝ), (∀ j, j ≠ i → x j = y j) →
    |f x - f y| ≤ L * |x i - y i|

theorem measurable_cons (n : ℕ) : Measurable (fun p : ℝ × (Fin n → ℝ) => prepend p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [prepend_zero] using measurable_fst
  · simpa only [prepend_succ, Function.comp_def] using (measurable_pi_apply j).comp measurable_snd

theorem bounded_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) : Integrable f μ := by
  refine (integrable_const B).mono' hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x

theorem integral_pi_succ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin (n + 1) => μ)) =
      ∫ z : Fin n → ℝ, ∫ u : ℝ, f (prepend u z) ∂μ ∂Measure.pi (fun _ => μ) := by
  have hi : Integrable (fun p : ℝ × (Fin n → ℝ) => f (prepend p.1 p.2))
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) :=
    bounded_integrable _ (hf.comp (measurable_cons n)) (fun p => hb _)
  have he := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).integral_comp' f
  have hh : (∫ x, f x ∂Measure.pi (fun _ : Fin (n + 1) => μ)) =
      ∫ p : ℝ × (Fin n → ℝ), f (prepend p.1 p.2) ∂μ.prod (Measure.pi (fun _ => μ)) := by
    simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq, prepend] using he.symm
  rw [hh, integral_prod_symm _ hi]

theorem head_lip {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} {L : ℝ}
    (hf : CoordinateLip f L) (z : Fin n → ℝ) (u v : ℝ) :
    |f (prepend u z) - f (prepend v z)| ≤ L * |u - v| := by
  have hsame : ∀ j : Fin (n + 1), j ≠ 0 → prepend u z j = prepend v z j := by
    intro j
    refine Fin.cases ?_ (fun k _ => by simp) j
    intro h
    exact (h rfl).elim
  simpa only [prepend_zero] using hf 0 (prepend u z) (prepend v z) hsame

theorem tail_lip {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} {L : ℝ}
    (hf : CoordinateLip f L) (u : ℝ) : CoordinateLip (fun z : Fin n → ℝ => f (prepend u z)) L := by
  intro i x y hxy
  have hsame : ∀ j : Fin (n + 1), j ≠ i.succ → prepend u x j = prepend u y j := by
    intro j
    refine Fin.cases (by intro _; simp) (fun k hk => ?_) j
    simpa only [prepend_succ] using hxy k (fun h => hk (congrArg Fin.succ h))
  simpa only [prepend_succ] using hf i.succ (prepend u x) (prepend u y) hsame

theorem product_weak (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hweak : ∀ f : ℝ → ℝ, Measurable f → (∀ x, |f x| ≤ B) →
      (∀ x y, |f x - f y| ≤ L * |x - y|) → |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ L * ε)
    (n : ℕ) {f : (Fin n → ℝ) → ℝ} (hmf : Measurable f) (hbf : ∀ x, |f x| ≤ B)
    (hcf : CoordinateLip f L) :
    |(∫ x, f x ∂Measure.pi (fun _ : Fin n => μ)) - ∫ x, f x ∂Measure.pi (fun _ : Fin n => ν)| ≤
      (n : ℝ) * L * ε := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty _ (0 : Fin 0 → ℝ), Measure.pi_of_empty _ (0 : Fin 0 → ℝ)]
    simp
  | succ n ih =>
    let g : (Fin n → ℝ) → ℝ := fun z => ∫ u, f (prepend u z) ∂ν
    have hmcons := measurable_cons n
    have hmJoint : Measurable (fun p : (Fin n → ℝ) × ℝ => f (prepend p.2 p.1)) :=
      hmf.comp (hmcons.comp measurable_swap)
    have hmg : Measurable g := hmJoint.stronglyMeasurable.integral_prod_right'.measurable
    have hbg : ∀ z, |g z| ≤ B := by
      intro z
      have hh := norm_integral_le_of_norm_le_const (μ := ν)
        (f := fun u => f (prepend u z))
        (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using hbf (prepend u z))
      simpa only [g, Real.norm_eq_abs, probReal_univ, mul_one] using hh
    have hislice (z : Fin n → ℝ) : Integrable (fun u => f (prepend u z)) ν :=
      bounded_integrable ν (hmf.comp (hmcons.comp (measurable_id.prodMk measurable_const))) (fun u => hbf _)
    have hcg : CoordinateLip g L := by
      intro i x y hxy
      change |(∫ u, f (prepend u x) ∂ν) - ∫ u, f (prepend u y) ∂ν| ≤ _
      rw [← integral_sub (hislice x) (hislice y)]
      have hp : ∀ u, |f (prepend u x) - f (prepend u y)| ≤ L * |x i - y i| :=
        fun u => tail_lip hcf u i x y hxy
      have hh := norm_integral_le_of_norm_le_const (μ := ν)
        (f := fun u => f (prepend u x) - f (prepend u y))
        (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using hp u)
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh
    have hiG := ih hmg hbg hcg
    let k : (Fin n → ℝ) → ℝ := fun z => ∫ u, f (prepend u z) ∂μ
    have hmk : Measurable k := hmJoint.stronglyMeasurable.integral_prod_right'.measurable
    have hbk : ∀ z, |k z| ≤ B := by
      intro z
      have hh := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun u => f (prepend u z))
        (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using hbf (prepend u z))
      simpa only [k, Real.norm_eq_abs, probReal_univ, mul_one] using hh
    have hpoint : ∀ z, |k z - g z| ≤ L * ε := by
      intro z
      exact hweak (fun u => f (prepend u z))
        (hmf.comp (hmcons.comp (measurable_id.prodMk measurable_const)))
        (fun u => hbf _) (head_lip hcf z)
    have hiK := bounded_integrable (Measure.pi (fun _ : Fin n => μ)) hmk hbk
    have hiGμ := bounded_integrable (Measure.pi (fun _ : Fin n => μ)) hmg hbg
    have hhead : |(∫ z, k z ∂Measure.pi (fun _ : Fin n => μ)) -
        ∫ z, g z ∂Measure.pi (fun _ : Fin n => μ)| ≤ L * ε := by
      rw [← integral_sub hiK hiGμ]
      have hh := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin n => μ))
        (f := fun z => k z - g z)
        (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hpoint z)
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh
    rw [integral_pi_succ μ hmf hbf, integral_pi_succ ν hmf hbf]
    change |(∫ z, k z ∂Measure.pi (fun _ : Fin n => μ)) -
      ∫ z, g z ∂Measure.pi (fun _ : Fin n => ν)| ≤ _
    have ht := abs_sub_le (∫ z, k z ∂Measure.pi (fun _ : Fin n => μ))
      (∫ z, g z ∂Measure.pi (fun _ : Fin n => μ)) (∫ z, g z ∂Measure.pi (fun _ : Fin n => ν))
    rw [Nat.cast_succ]
    nlinarith only [ht, hhead, hiG]

theorem euclidean_coordinateLip {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hf : ∀ x y, |f x - f y| ≤ L * dist x y) :
    CoordinateLip (fun x : Fin n → ℝ => f (WithLp.toLp 2 x)) L := by
  intro i x y hxy
  let X : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  have hsq : ‖X - Y‖ ^ 2 = (x i - y i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j : Fin n, (x j - y j) ^ 2) = (x i - y i) ^ 2
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hji
      rw [hxy j hji, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hn : ‖X - Y‖ = |x i - y i| := by
    apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1
    rw [sq_abs]
    exact hsq
  have hh := hf X Y
  rw [dist_eq_norm, hn] at hh
  exact hh

theorem euclidean_product_weak (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hweak : ∀ f : ℝ → ℝ, Measurable f → (∀ x, |f x| ≤ B) →
      (∀ x y, |f x - f y| ≤ L * |x - y|) → |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ L * ε)
    (n : ℕ) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hmf : Measurable f) (hbf : ∀ x, |f x| ≤ B)
    (hcf : ∀ x y, |f x - f y| ≤ L * dist x y) :
    |(∫ x, f x ∂(Measure.pi (fun _ : Fin n => μ)).map (WithLp.toLp 2)) -
        ∫ x, f x ∂(Measure.pi (fun _ : Fin n => ν)).map (WithLp.toLp 2)| ≤ (n : ℝ) * L * ε := by
  rw [integral_map (by fun_prop) hmf.aestronglyMeasurable,
    integral_map (by fun_prop) hmf.aestronglyMeasurable]
  exact product_weak μ ν hL hε hweak n (hmf.comp (WithLp.measurable_toLp 2 (Fin n → ℝ)))
    (fun x => hbf _) (euclidean_coordinateLip hcf)

theorem variance_two_map (n : ℕ) :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun z => Real.sqrt 2 • z) =
      (Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 2)).map (WithLp.toLp 2) := by
  have hscale : (ProbabilityTheory.gaussianReal 0 1).map (fun x : ℝ => Real.sqrt 2 * x) =
      ProbabilityTheory.gaussianReal 0 2 := by
    have hh := ProbabilityTheory.gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt 2)
    have hv : NNReal.mk ((Real.sqrt 2) ^ 2) (sq_nonneg _) * (1 : ℝ≥0) = 2 := by
      apply NNReal.eq
      change (Real.sqrt (2 : ℝ)) ^ 2 * 1 = 2
      rw [mul_one, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [mul_zero, hv] at hh
    exact hh
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)).map
    (fun x => Real.sqrt 2 • WithLp.toLp 2 x) = _
  have he : (fun x : Fin n → ℝ => Real.sqrt 2 • WithLp.toLp 2 x) =
      fun x => WithLp.toLp 2 (fun i => Real.sqrt 2 * x i) := by
    funext x
    ext i
    rfl
  rw [he]
  have hcomp := Measure.map_map (μ := Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))
    (WithLp.measurable_toLp 2 (Fin n → ℝ))
    (show Measurable (fun x : Fin n → ℝ => fun i => Real.sqrt 2 * x i) by fun_prop)
  simp only [Function.comp_def] at hcomp
  rw [← hcomp, Measure.pi_map_pi (fun _ => by fun_prop)]
  simp_rw [hscale]

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

def roundedOperator (ν : Measure E) (T : E → E) (σ : ℝ) (round : E → E)
    (f : E → ℝ) (x : E) : ℝ :=
  operator ν T σ (fun y => f (round y)) x

theorem bounded (ν : Measure E) [IsProbabilityMeasure ν]
    {T round : E → E} (hT : Measurable T) (hr : Measurable round) (σ : ℝ)
    {f : E → ℝ} {B : ℝ} (hmf : Measurable f) (hbf : ∀ x, |f x| ≤ B) :
    Measurable (roundedOperator ν T σ round f) ∧
      ∀ x, |roundedOperator ν T σ round f x| ≤ B := by
  exact ⟨measurable_operator ν hT σ (hmf.comp hr),
    operator_bound ν T σ (fun y => hbf (round y))⟩

theorem supnorm_nonexpansive (ν : Measure E) [IsProbabilityMeasure ν]
    (T : E → E) (σ : ℝ) {round : E → E} (hr : Measurable round)
    {f g : E → ℝ} {B D : ℝ} (hmf : Measurable f) (hmg : Measurable g)
    (hbf : ∀ x, |f x| ≤ B) (hbg : ∀ x, |g x| ≤ B)
    (hd : ∀ x, |f x - g x| ≤ D) (x : E) :
    |roundedOperator ν T σ round f x - roundedOperator ν T σ round g x| ≤ D := by
  exact NoiseOperator.supnorm_nonexpansive ν T σ (hmf.comp hr) (hmg.comp hr)
    (fun y => hbf _) (fun y => hbg _) (fun y => hd _) x

theorem rounding_error (ν : Measure E) [IsProbabilityMeasure ν]
    (T : E → E) (σ : ℝ) {round : E → E} (hr : Measurable round)
    {er B L : ℝ} {f : E → ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L)
    (he : ∀ y, dist (round y) y ≤ er) (x : E) :
    |roundedOperator ν T σ round f x - operator ν T σ f x| ≤ L * er := by
  change |(∫ z, f (round (T x + σ • z)) ∂ν) - ∫ z, f (T x + σ • z) ∂ν| ≤ _
  rw [← integral_sub
    (bounded_integrable_noise ν (T := T) (σ := σ) (f := fun y => f (round y))
      (hf.1.comp hr) (fun y => hf.2.1 _) x)
    (bounded_integrable_noise ν (T := T) (σ := σ) hf.1 hf.2.1 x)]
  have hp : ∀ z, |f (round (T x + σ • z)) - f (T x + σ • z)| ≤ L * er := by
    intro z
    exact (hf.2.2 _ _).trans (mul_le_mul_of_nonneg_left (he _) hL)
  have hh := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun z => f (round (T x + σ • z)) - f (T x + σ • z))
    (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hp z)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh

theorem one_step_error (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T T' : E → E) (σ : ℝ) {round : E → E} (hr : Measurable round)
    {er ed ε : ℝ}
    (hround : ∀ y, dist (round y) y ≤ er) (hT : ∀ x, dist (T x) (T' x) ≤ ed)
    (hnoise : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      |(∫ z, f z ∂μ) - ∫ z, f z ∂ν| ≤ L * ε)
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) (x : E) :
    |roundedOperator ν T σ round f x - operator μ T' σ f x| ≤
      L * (er + ed + |σ| * ε) := by
  have h₁ := rounding_error ν T σ hr hL hf hround x
  have h₂ := drift_perturbation ν T T' σ hL hf hT x
  have h₃ := noise_perturbation μ ν T' σ ε hnoise hL hf x
  rw [abs_sub_comm (operator μ T' σ f x)] at h₃
  have ht₁ := abs_sub_le (roundedOperator ν T σ round f x)
    (operator ν T σ f x) (operator ν T' σ f x)
  have ht₂ := abs_sub_le (roundedOperator ν T σ round f x)
    (operator ν T' σ f x) (operator μ T' σ f x)
  nlinarith only [h₁, h₂, h₃, ht₁, ht₂]

def eulerDrift (g : E → E) (s : ℝ) (x : E) : E := x - s ^ 2 • g x

theorem euler_drift_error {g ĝ : E → E} {s eg : ℝ}
    (hg : ∀ x, dist (ĝ x) (g x) ≤ eg) (x : E) :
    dist (eulerDrift ĝ s x) (eulerDrift g s x) ≤ s ^ 2 * eg := by
  change dist (x - s ^ 2 • ĝ x) (x - s ^ 2 • g x) ≤ _
  rw [dist_sub_left, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]
  exact mul_le_mul_of_nonneg_left (hg x) (sq_nonneg s)

theorem euler_one_step (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g ĝ round : E → E} (hr : Measurable round) {s eg er ε : ℝ} (hs : 0 ≤ s)
    (hg : ∀ x, dist (ĝ x) (g x) ≤ eg) (hround : ∀ y, dist (round y) y ≤ er)
    (hnoise : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      |(∫ z, f z ∂μ) - ∫ z, f z ∂ν| ≤ L * ε)
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) (x : E) :
    |roundedOperator ν (eulerDrift ĝ s) s round f x - operator μ (eulerDrift g s) s f x| ≤
      L * (s ^ 2 * eg + s * ε + er) := by
  have hh := one_step_error μ ν (eulerDrift ĝ s) (eulerDrift g s) s hr
    hround (euler_drift_error hg) hnoise hL hf x
  rw [abs_of_nonneg hs] at hh
  nlinarith only [hh]

theorem euler_one_step_standard (Γ ν : Measure E) [IsProbabilityMeasure Γ] [IsProbabilityMeasure ν]
    {g ĝ round : E → E} (hr : Measurable round) {s eg er ε : ℝ} (hs : 0 ≤ s)
    (hg : ∀ x, dist (ĝ x) (g x) ≤ eg) (hround : ∀ y, dist (round y) y ≤ er)
    (hnoise : ∀ (f : E → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip f B L →
      |(∫ z, f z ∂Γ.map (fun z => Real.sqrt 2 • z)) - ∫ z, f z ∂ν| ≤ L * ε)
    {f : E → ℝ} {B L : ℝ} (hL : 0 ≤ L) (hf : BoundedLip f B L) (x : E) :
    |roundedOperator ν (eulerDrift ĝ s) s round f x -
      operator Γ (eulerDrift g s) (Real.sqrt 2 * s) f x| ≤
      L * (s ^ 2 * eg + s * ε + er) := by
  letI : IsProbabilityMeasure (Γ.map (fun z : E => Real.sqrt 2 • z)) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable (fun z : E => Real.sqrt 2 • z)).aemeasurable
  have hh := euler_one_step (Γ.map (fun z => Real.sqrt 2 • z)) ν hr hs hg hround hnoise hL hf x
  rw [operator_map_smul Γ (eulerDrift g s) s (Real.sqrt 2) hf.1 x, mul_comm s] at hh
  exact hh

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

theorem realNoise_map {N : ℕ} (D : EulerData N) :
    (uniformBits (N*gaussianNoiseBits D.k)).map D.realNoise = noiseLaw D := by
  exact product_bitLaw N (gaussianNoiseBits D.k)
    (fun ω => (gaussianDraw (D.k,List.ofFn ω):ℝ))

theorem operator_eq {N : ℕ} (D : EulerData N) (S : SpinLaw) (f : Point N → ℝ) (hf : Measurable f) :
    D.operator S f = RoundedEuler.roundedOperator (noiseLaw D)
      (RoundedEuler.eulerDrift (rationalDrift S D.L D.h D.sCap D.a D.dPhi D.snap) (D.sigma:ℝ))
      (D.sigma:ℝ) (roundPoint (D.dRound:ℝ)) f := by
  funext z
  unfold RoundedEuler.roundedOperator NoiseOperator.operator
  rw [← realNoise_map D]
  have hm : Measurable (fun y : Point N => f (roundPoint (D.dRound:ℝ)
      (RoundedEuler.eulerDrift (rationalDrift S D.L D.h D.sCap D.a D.dPhi D.snap) (D.sigma:ℝ) z +
        (D.sigma:ℝ) • y))) :=
    hf.comp ((roundPoint_measurable N D.dRound).comp
      (measurable_const.add (measurable_id.const_smul (D.sigma:ℝ))))
  rw [integral_map (measurable_of_finite _).aemeasurable hm.aestronglyMeasurable, integral_uniformBits]
  simp only [EulerData.operator,finiteOperator,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,
    Nat.cast_pow,Nat.cast_ofNat]
  rfl

theorem operator_bounded {N : ℕ} (D : EulerData N) (S : SpinLaw)
    (f : Point N → ℝ) (B : ℝ) (hf : Measurable f) (hb : ∀ z, |f z| ≤ B) :
    Measurable (D.operator S f) ∧ ∀ z, |D.operator S f z| ≤ B := by
  rw [operator_eq D S f hf]
  have hT : Measurable (RoundedEuler.eulerDrift
      (rationalDrift S D.L D.h D.sCap D.a D.dPhi D.snap) (D.sigma:ℝ)) := by
    change Measurable (fun z : Point N => z-(D.sigma:ℝ)^2 •
      rationalDrift S D.L D.h D.sCap D.a D.dPhi D.snap z)
    exact measurable_id.sub ((rationalDrift_measurable S D.L D.h D.sCap D.a D.dPhi D.snap).const_smul ((D.sigma:ℝ)^2))
  exact RoundedEuler.bounded (noiseLaw D) hT (roundPoint_measurable N D.dRound) _ hf hb

theorem operator_nonexpansive {N : ℕ} (D : EulerData N) (S : SpinLaw)
    (f g : Point N → ℝ) (B E : ℝ) (hf : Measurable f) (hg : Measurable g)
    (hbf : ∀ z, |f z| ≤ B) (hbg : ∀ z, |g z| ≤ B) (he : ∀ z, |f z-g z| ≤ E) :
    ∀ z, |D.operator S f z-D.operator S g z| ≤ E := by
  rw [operator_eq D S f hf,operator_eq D S g hg]
  exact RoundedEuler.supnorm_nonexpansive (noiseLaw D) _ _ (roundPoint_measurable N D.dRound)
    hf hg hbf hbg he

theorem noise_weak {N : ℕ} (D : EulerData N) (f : Point N → ℝ) (B L : ℝ)
    (hL : 0 ≤ L) (hf : BoundedLip f B L) :
    |(∫ z, f z ∂(stdGaussian (Point N)).map (fun z => Real.sqrt 2 • z))-
      ∫ z, f z ∂noiseLaw D| ≤ L*((N:ℝ)/((D.k:ℝ)+1)) := by
  have h1 : ∀ g : ℝ → ℝ, Measurable g → (∀ x, |g x| ≤ B) →
      (∀ x y, |g x-g y| ≤ L*|x-y|) →
      |(∫ x, g x ∂gaussianReal 0 2)-∫ x, g x ∂gaussianNoiseLaw D.k| ≤ L*(1/((D.k:ℝ)+1)) := by
    intro g _ _ hgl
    have hl : LipschitzWith ⟨L,hL⟩ g := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change |g x-g y| ≤ L*|x-y|
      exact hgl x y
    have hh := gaussianNoiseLaw_weak D.k L hL g hl
    have he : L/((D.k:ℝ)+1) = L*(1/((D.k:ℝ)+1)) := by ring
    rw [he] at hh
    simpa only [abs_sub_comm] using hh
  have hv := ProductWeak.euclidean_product_weak (gaussianReal 0 2) (gaussianNoiseLaw D.k)
    hL (by positivity : (0:ℝ) ≤ 1/((D.k:ℝ)+1)) h1 N hf.1 hf.2.1 hf.2.2
  rw [← ProductWeak.variance_two_map N] at hv
  have he : (N:ℝ)*L*(1/((D.k:ℝ)+1)) = L*((N:ℝ)/((D.k:ℝ)+1)) := by ring
  rw [he] at hv
  exact hv

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

theorem stepError_nonneg {N : ℕ} (S : SpinLaw) (D : EulerData N) {B : ℝ}
    (hB : 0 ≤ B) (hd : 0 ≤ D.dPhi) (hsnap : 0 ≤ D.snap)
    (hsigma : 0 ≤ D.sigma) (hr : 0 ≤ D.dRound) : 0 ≤ stepError S D B := by
  have hρ : (0:ℝ) < S.ρ 1 := by exact_mod_cast S.pos 1 S.one_mem
  have hdR : (0:ℝ) ≤ D.dPhi := by exact_mod_cast hd
  have hsnapR : (0:ℝ) ≤ D.snap := by exact_mod_cast hsnap
  have hsigmaR : (0:ℝ) ≤ D.sigma := by exact_mod_cast hsigma
  have hrR : (0:ℝ) ≤ D.dRound := by exact_mod_cast hr
  unfold stepError driftError
  positivity

theorem operator_step_error {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (D : EulerData N)
    (hs : tau S < (D.sCap:ℝ)) (ha : 0 ≤ D.a) (ha1 : D.a ≤ 1)
    (hPSD : ((D.sCap:ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM D.L*(castM D.L).transpose).PosSemidef)
    (hd : 0 < D.dPhi) (hd1 : D.dPhi ≤ 1) (hsnap : 0 < D.snap)
    (hr : 0 < D.dRound) (hsigma : 0 ≤ D.sigma) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ i j, |(D.L i j:ℝ)| ≤ B)
    (f : Point N → ℝ) (Bf L : ℝ) (hLip : 0 ≤ L) (hf : BoundedLip f Bf L) (z : Point N) :
    |D.operator S f z - NoiseOperator.operator (stdGaussian (Point N))
      (LangevinAlgebra.drift (gradient S D.sCap D.a (castM D.L) (castV D.h)) ((D.sigma:ℝ)^2))
      (Real.sqrt 2*(D.sigma:ℝ)) f z| ≤ L*stepError S D B := by
  have hG (x : Point N) : dist (rationalDrift S D.L D.h D.sCap D.a D.dPhi D.snap x)
      (gradient S D.sCap D.a (castM D.L) (castV D.h) x) ≤ driftError S D B := by
    rw [dist_eq_norm]
    exact rationalDrift_error S hS D.L D.h D.sCap D.a D.dPhi D.snap hs ha ha1 hPSD hd hd1 hsnap B hB hL x
  have hR (x : Point N) : dist (roundPoint (D.dRound:ℝ) x) x ≤ ((N:ℝ)+1)*(D.dRound:ℝ) := by
    rw [dist_eq_norm]
    exact roundPoint_error _ (by exact_mod_cast hr) x
  have hNoise : ∀ (g : Point N → ℝ) (B L : ℝ), 0 ≤ L → BoundedLip g B L →
      |(∫ x, g x ∂(stdGaussian (Point N)).map (fun z => Real.sqrt 2 • z))-
        ∫ x, g x ∂noiseLaw D| ≤ L*((N:ℝ)/((D.k:ℝ)+1)) := noise_weak D
  have ht := RoundedEuler.euler_one_step_standard (stdGaussian (Point N)) (noiseLaw D)
    (roundPoint_measurable N D.dRound) (by exact_mod_cast hsigma : (0:ℝ) ≤ D.sigma)
    hG hR hNoise hLip hf z
  rw [operator_eq D S f hf.1]
  exact ht

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
  have haReal : (0:ℝ) < D.a := by exact_mod_cast ha
  have hsReal : (0:ℝ) < D.sigma := by exact_mod_cast hsigma
  have hAdmit := schedule_admissible hR (by exact_mod_cast ha1 : (D.a:ℝ) ≤ 1) haR hsReal hsR
  have hE0 := stepError_nonneg S D hB hd.le hsnap.le hsigma.le hr.le
  have hApprox : ∀ (g : Point N → ℝ) (Bf L : ℝ), 0 ≤ L → BoundedLip g Bf L →
      ∀ x, |D.operator S g x - NoiseOperator.operator (stdGaussian (Point N))
        (LangevinAlgebra.drift cert.g ((D.sigma:ℝ)^2)) (Real.sqrt 2*(D.sigma:ℝ)) g x| ≤ L*stepError S D B := by
    intro g Bf L hLip hg x
    rw [hGeq]
    exact operator_step_error S hS D hs ha.le ha1 hPSD hd hd1 hsnap hr hsigma.le B hB hL g Bf L hLip hg x
  have hw := LangevinBudget.weak_bound cert haReal hsReal hAdmit.1 hE0 hAdmit.2.1 hAdmit.2.2
    hR haR hsR hError hM hH (D.operator S) (operator_bounded D S) (operator_nonexpansive D S)
    hApprox hLip hLR hf T hT
  rw [EulerData.integral_trajectoryLaw D S T (0 : Fin N → ℚ) f hf.1]
  have hz : WithLp.toLp 2 (castV (0 : Fin N → ℚ)) = (0 : Point N) := by ext i; simp [castV]
  rw [hz,← hUeq]
  exact hw

end CritWinSpin.Implementation.EulerAnalyticStep
end

end



set_option autoImplicit false
set_option linter.all false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory ProbabilityTheory CritWinSpin
open CritWinSpin.LocalTM2.Compiled CritWinSpin.Implementation
open EnvelopeGeometry LangevinBudget

theorem solution {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (D : EulerData N)
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
    (hError :
      (D.sigma:ℝ)^2 * (((N:ℝ)+1)*((N:ℝ)*B*
        (2*(Fintype.card {x:ℚ // x∈S.A}:ℝ)*(D.dPhi:ℝ)/(S.ρ 1:ℝ))+2*(D.snap:ℝ))) +
        (D.sigma:ℝ)*((N:ℝ)/((D.k:ℝ)+1))+((N:ℝ)+1)*(D.dRound:ℝ) ≤
      (D.sigma:ℝ)^2/(16*R^3))
    (hM : (∫ x, ‖x‖ ∂DensityAnalysis.gibbs cert.U) ≤ R)
    (hH : 2+(∫ x, ‖cert.g x‖^6 ∂DensityAnalysis.gibbs cert.U)+
      GaussianMoments.sixthConstant*(N:ℝ)^3 ≤ R)
    (T : ℕ) (hT : 16*R^4/(D.sigma:ℝ)^2 ≤ (T:ℝ))
    (f : DensityAnalysis.Point N → ℝ) (Bf L : ℝ) (hLip : 0 ≤ L) (hLR : L ≤ R) (hf : Measurable f) (hfB : ∀ x, |f x| ≤ Bf)
    (hfL : ∀ x y, |f x-f y| ≤ L*dist x y) :
    |(∫ x, f x ∂D.trajectoryLaw S T (0 : Fin N → ℚ))-
      ∫ x, f x ∂DensityAnalysis.gibbs (potential S D.sCap D.a (castM D.L) (castV D.h))| ≤ 1/(2*R) := by
  have he : EulerAnalyticStep.stepError S D B ≤ (D.sigma:ℝ)^2/(16*R^3) := by
    simpa only [EulerAnalyticStep.stepError,EulerAnalyticStep.driftError] using hError
  exact EulerAnalyticStep.trajectory_weak S hS D hs ha ha1 hPSD hd hd1 hsnap hr hsigma B hB hL
    cert hUeq hGeq hR haR hsR he hM hH T hT f Bf L hLip hLR ⟨hf,hfB,hfL⟩

#print axioms solution
