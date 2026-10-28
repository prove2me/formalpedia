-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:39.796377+00:00
-- url     : https://prove2.me/submissions/4dbdc9d2-4e6c-4a0f-a88f-84c05b16af10

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Temperate
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cutoff_eq_one_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_hasCompactSupport_cutoff_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_of_norm_le_pow_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_iteratedFDeriv_cutoff_le_readable

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- Product rule for the gradient. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  unfold gradient
  rw [fderiv_fun_mul hf hg, map_add, map_smulₛₗ, map_smulₛₗ]
  simp
end Gradient
end DifferentialTools
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff (R : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) R) := by
    change ContDiff ℝ ∞
      (fun x : E => (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x))
    exact unitBump.contDiff.comp (contDiff_const_smul R⁻¹)
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.abs_cutoff_le_one (R : ℝ) (x : E) : |cutoff R x| ≤ 1 := by
    change |(unitBump : ContDiffBump (0 : E)) (R⁻¹ • x)| ≤ 1
    have hnonneg :
        0 ≤ (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x) :=
      ContDiffBump.nonneg (unitBump : ContDiffBump (0 : E))
    have hle :
        (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x) ≤ 1 :=
      ContDiffBump.le_one (unitBump : ContDiffBump (0 : E))
    exact abs_le.2 ⟨by linarith, hle⟩
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖∇g(x)‖ = ‖∇¹g(x)‖`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one (g : E → ℝ) (x : E) :
    ‖gradient g x‖ = ‖iteratedFDeriv ℝ 1 g x‖ := by
    rw [gradient, (InnerProductSpace.toDual ℝ E).symm.norm_map,
      norm_iteratedFDeriv_one]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
end
end
end

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
open scoped ContDiff
open Filter Topology FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
section StructuredSpace
variable {F : Type*}
variable [NormedAddCommGroup F]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V]
    [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private theorem FunctionalInequalities.KLS.LogConcave.q_memLp_of_polynomial_bound {g : V → F}
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (hg : AEStronglyMeasurable g (ν : Measure V))
    {C : ℝ} {k : ℕ}
    (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
    MemLp g 2 (ν : Measure V) := by
  apply (memLp_two_iff_integrable_sq_norm hg).mpr
  apply integrable_of_norm_le_pow_readable (ν : Measure V) hexp (hg.norm.pow 2)
    (C := C ^ 2) (k := k * 2)
  intro x
  change ‖‖g x‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private theorem FunctionalInequalities.KLS.LogConcave.q_tendsto_toLp [InnerProductSpace ℝ F]
    {a : ℕ → V → F} {b : V → F}
    (ha : ∀ n, MemLp (a n) 2 (ν : Measure V))
    (hb : MemLp b 2 (ν : Measure V))
    {D : V → ℝ} (hD : Integrable D (ν : Measure V))
    (hbound : ∀ n x, ‖a n x - b x‖ ^ 2 ≤ D x)
    (hlocal : ∀ x, ∀ᶠ n : ℕ in atTop, a n x = b x) :
    Tendsto (fun n => (ha n).toLp (a n)) atTop (𝓝 (hb.toLp b)) := by
  have ht : Tendsto (fun n => ∫ x, ‖a n x - b x‖ ^ 2 ∂(ν : Measure V))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_integral_of_dominated_convergence
      (F := fun n x => ‖a n x - b x‖ ^ 2) (f := fun _ => (0 : ℝ)) D
      (fun n => ((ha n).1.sub hb.1).norm.pow 2) hD
      (fun n => ae_of_all _ (fun x => by
        simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hbound n x))
      (ae_of_all _ (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [hlocal x] with n hn
        simp [hn]))
  have heq (n : ℕ) :
      ‖(ha n).toLp (a n) - hb.toLp b‖ ^ 2 =
        ∫ x, ‖a n x - b x‖ ^ 2 ∂(ν : Measure V) := by
    rw [← real_inner_self_eq_norm_sq, ← (ha n).toLp_sub hb, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [((ha n).sub hb).coeFn_toLp] with x hx
    rw [hx, Pi.sub_apply, real_inner_self_eq_norm_sq]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, ← heq, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using hs
private theorem FunctionalInequalities.KLS.LogConcave.q_sq_sub_le {u v : F} {B : ℝ}
    (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) : ‖u - v‖ ^ 2 ≤ (2 * B) ^ 2 := by
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  calc
    ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add hu hv
    _ = 2 * B := by ring
end StructuredSpace
include hexp in
/-- A function of temperate growth has its `L²(ν)` class in the domain of the closed unit gradient,
which sends it to the class of `∇f` (only the exponential moments of `ν` are used). -/
theorem solution {f : V → ℝ}
    (hf : f.HasTemperateGrowth) :
    ∃ (hf2 : MemLp f 2 (ν : Measure V)) (hg2 : MemLp (gradient f) 2 (ν : Measure V))
      (hmem : hf2.toLp f ∈ (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem⟩ = hg2.toLp (gradient f) := by
  obtain ⟨k, C, hC, hb⟩ := hf.norm_iteratedFDeriv_le_uniform 1
  have hfb (x : V) : ‖f x‖ ≤ C * (1 + ‖x‖) ^ k := by
    simpa only [norm_iteratedFDeriv_zero] using hb 0 (by omega) x
  have hgb (x : V) : ‖gradient f x‖ ≤ C * (1 + ‖x‖) ^ k := by
    simpa only [FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one] using hb 1 le_rfl x
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf2 := FunctionalInequalities.KLS.LogConcave.q_memLp_of_polynomial_bound hexp hf.1.continuous.aestronglyMeasurable hfb
  have hg2 := FunctionalInequalities.KLS.LogConcave.q_memLp_of_polynomial_bound hexp
    (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hf1).aestronglyMeasurable hgb
  obtain ⟨K₀, hK₀⟩ := FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_cutoff_le_readable (E := V) 1
  let K : ℝ := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  let A : ℝ := C + C * K
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCA : C ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (mul_nonneg hC hK)
  let a : ℕ → V → ℝ := fun n x => FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x * f x
  have ha (n : ℕ) : ContDiff ℝ ∞ (a n) := (FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff _).mul hf.1
  have hac (n : ℕ) : HasCompactSupport (a n) :=
    (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_cutoff_readable (by positivity : 0 < (n : ℝ) + 1)).mul_right
  have hab (n : ℕ) (x : V) : ‖a n x‖ ≤ A * (1 + ‖x‖) ^ k := by
    dsimp only [a]
    rw [norm_mul]
    calc
      _ ≤ 1 * (C * (1 + ‖x‖) ^ k) :=
        mul_le_mul (by simpa only [Real.norm_eq_abs] using FunctionalInequalities.Analysis.BakryEmery.abs_cutoff_le_one _ _)
          (hfb x) (norm_nonneg _) zero_le_one
      _ ≤ A * (1 + ‖x‖) ^ k := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right hCA (by positivity)
  have hgab (n : ℕ) (x : V) : ‖gradient (a n) x‖ ≤ A * (1 + ‖x‖) ^ k := by
    have hc1 : ContDiff ℝ 1 (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) : V → ℝ) :=
      (FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff _).of_le (WithTop.coe_le_coe.mpr le_top)
    have hcut : ‖gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ ≤ K := by
      rw [FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one]
      exact (hK₀ _
        (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n : ℝ) + 1) x).trans
        (le_max_left _ _)
    dsimp only [a]
    rw [FunctionalInequalities.Analysis.BakryEmery.gradient_mul (hc1.differentiable (by norm_num) x)
      (hf1.differentiable (by norm_num) x)]
    calc
      _ ≤ ‖FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x • gradient f x‖ +
          ‖f x • gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ := norm_add_le _ _
      _ = |FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x| * ‖gradient f x‖ +
          |f x| * ‖gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (C * (1 + ‖x‖) ^ k) + (C * (1 + ‖x‖) ^ k) * K := by
        gcongr
        · exact FunctionalInequalities.Analysis.BakryEmery.abs_cutoff_le_one _ _
        · exact hgb x
        · simpa only [Real.norm_eq_abs] using hfb x
      _ = _ := by dsimp [A]; ring
  have hfA (x : V) : ‖f x‖ ≤ A * (1 + ‖x‖) ^ k :=
    (hfb x).trans (mul_le_mul_of_nonneg_right hCA (by positivity))
  have hgA (x : V) : ‖gradient f x‖ ≤ A * (1 + ‖x‖) ^ k :=
    (hgb x).trans (mul_le_mul_of_nonneg_right hCA (by positivity))
  let D : V → ℝ := fun x => (2 * A) ^ 2 * (1 + ‖x‖) ^ (k * 2)
  have hD : Integrable D (ν : Measure V) := by
    apply FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_readable _ hexp (by fun_prop)
      (C := (2 * A) ^ 2) (k := k * 2)
    intro x
    exact Real.norm_of_nonneg (by dsimp [D]; positivity) |>.le
  have hlocal (x : V) : ∀ᶠ n : ℕ in atTop, a n =ᶠ[𝓝 x] f := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hx : ‖x‖ < (n : ℝ) + 1 := by linarith
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    dsimp only [a]
    rw [FunctionalInequalities.Analysis.BakryEmery.cutoff_eq_one_readable (by positivity) hy.le, one_mul]
  have hat := FunctionalInequalities.KLS.LogConcave.q_tendsto_toLp
    (fun n => FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (ha n) (hac n))
    hf2 hD (fun n x => by
      simpa only [D, mul_pow, pow_mul, mul_assoc] using FunctionalInequalities.KLS.LogConcave.q_sq_sub_le (hab n x) (hfA x))
    (fun x => (hlocal x).mono (fun _ hn => hn.eq_of_nhds))
  have hgat := FunctionalInequalities.KLS.LogConcave.q_tendsto_toLp
    (fun n => FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (ha n) (hac n))
    hg2 hD (fun n x => by
      simpa only [D, mul_pow, pow_mul, mul_assoc] using FunctionalInequalities.KLS.LogConcave.q_sq_sub_le (hgab n x) (hgA x))
    (fun x => (hlocal x).mono (fun _ hn => hn.gradient_eq))
  have hmem (n : ℕ) := hν.toLp_mem_closedWeightedOperator_domain m hi (ha n) (hac n)
  have hgt : Tendsto (fun n =>
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem n⟩)
      atTop (𝓝 (hg2.toLp (gradient f))) := by
    convert hgat using 1
    apply funext
    intro n
    exact hν.closedWeightedOperator_toLp_eq m hi (ha n) (hac n)
  obtain ⟨hmemf, heq⟩ := FunctionalInequalities.Analysis.Semigroup.exists_mem_domain_apply_eq_of_tendsto
    (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi) hmem hat hgt
  exact ⟨hf2, hg2, hmemf, heq⟩
