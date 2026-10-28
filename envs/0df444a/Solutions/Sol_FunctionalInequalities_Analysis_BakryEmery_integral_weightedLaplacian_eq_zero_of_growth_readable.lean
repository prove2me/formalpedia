-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero_of_growth_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:39.652825+00:00
-- url     : https://prove2.me/submissions/df25459b-ad29-43ee-85bc-82384e60b021

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_abs_laplacian_le_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cutoff_eq_one_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_hasCompactSupport_cutoff_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_of_norm_le_pow_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_laplacian_mul_readable
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
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gamma
variable [CompleteSpace E]
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_apply (f g : E → ℝ) (x : E) : gamma f g x = ⟪gradient f x, gradient g x⟫ := rfl
variable [FiniteDimensional ℝ E]
/-- Product rule for the weighted Laplacian: `ℒ(fg) = f ℒg + g ℒf + 2 Γ(f, g)`, for `C²` `f`, `g`
and an arbitrary potential `U`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_mul (U : E → ℝ) {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : E) :
    weightedLaplacian U (fun y => f y * g y) x =
      f x * weightedLaplacian U g x + g x * weightedLaplacian U f x + 2 * gamma f g x := by
  simp only [weightedLaplacian_apply, gamma_apply]
  rw [laplacian_mul_readable hf hg x, gradient_mul (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x), inner_add_right, inner_smul_right, inner_smul_right]
  ring
end Gamma
end
end
end

section
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
/-- The generator integrates to zero: `∫ ℒ_W f dμ_W = 0` for `μ_W = m.tilted (-W)`, `W ∈ C¹` and a
compactly supported `C²` function `f`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero {W f : E → ℝ} (hW : ContDiff ℝ 1 W)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x, weightedLaplacian W f x ∂(m.tilted (-W)) = 0 := by
    have h :=
      integral_inner_gradient_tilted m hW hf hfc
        (g := fun _ : E => (1 : ℝ)) contDiff_const
    simp at h
    have h' : -(∫ x, weightedLaplacian W f x ∂(m.tilted (-W))) = 0 := by
      simpa only [integral_neg] using h.symm
    exact neg_eq_zero.mp h'
open Filter Topology
universe v
end
end
end

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
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
omit [MeasurableSpace E] [BorelSpace E] in
/-- The weighted Laplacian is local: functions agreeing near `x` have the same `ℒ` at `x`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_congr_of_eventuallyEq (V : E → ℝ) {f g : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] g) : weightedLaplacian V f x = weightedLaplacian V g x := by
  rw [weightedLaplacian_apply, weightedLaplacian_apply, h.gradient_eq,
    (InnerProductSpace.laplacian_congr_nhds h).eq_of_nhds]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
omit [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.growth_abs_weightedLaplacian_le (V g : E → ℝ) (x : E) :
    |weightedLaplacian V g x| ≤
      (Module.finrank ℝ E : ℝ) * ‖iteratedFDeriv ℝ 2 g x‖ +
        ‖gradient V x‖ * ‖iteratedFDeriv ℝ 1 g x‖ := by
  rw [weightedLaplacian_apply]
  calc
    |Laplacian.laplacian g x - ⟪gradient V x, gradient g x⟫| ≤
        |Laplacian.laplacian g x| + |⟪gradient V x, gradient g x⟫| :=
      abs_sub _ _
    _ ≤ _ := by
      gcongr
      · exact abs_laplacian_le_readable g x
      · simpa only [norm_gradient_eq_norm_iteratedFDeriv_one] using
          abs_real_inner_le_norm (gradient V x) (gradient g x)
omit [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.growth_weightedLaplacian_bound {V g : E → ℝ}
    {CV C : ℝ} {kV k : ℕ} (hCV : 0 ≤ CV) (hC : 0 ≤ C)
    (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hg : ∀ x, ‖iteratedFDeriv ℝ 1 g x‖ ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 2 g x‖ ≤ C * (1 + ‖x‖) ^ k) (x : E) :
    |weightedLaplacian V g x| ≤
      ((Module.finrank ℝ E : ℝ) * C + CV * C) * (1 + ‖x‖) ^ (k + kV) := by
  have hp : 1 ≤ (1 + ‖x‖) ^ kV := one_le_pow₀ (by linarith [norm_nonneg x])
  calc
    |weightedLaplacian V g x| ≤
        (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) +
          (CV * (1 + ‖x‖) ^ kV) * (C * (1 + ‖x‖) ^ k) := by
      apply (growth_abs_weightedLaplacian_le V g x).trans
      gcongr
      · exact (hg x).2
      · exact hVg x
      · exact (hg x).1
    _ ≤
        (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) * (1 + ‖x‖) ^ kV +
          (CV * (1 + ‖x‖) ^ kV) * (C * (1 + ‖x‖) ^ k) := by
      have hm : (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) ≤
          (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) * (1 + ‖x‖) ^ kV :=
        le_mul_of_one_le_right (by positivity) hp
      exact add_le_add_left hm _
    _ = _ := by rw [pow_add]; ring
/-- `∫ ℒf dμ = 0` for `μ = m.tilted (-V)` with `V ∈ C¹`, `∇V` polynomially bounded and all
exponential moments, and `f ∈ C²` with `f`, `∇f`, `∇²f` polynomially bounded. -/
theorem solution {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
    {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : ContDiff ℝ 2 f) {C : ℝ} {k : ℕ}
    (hfg : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ k ∧ ‖iteratedFDeriv ℝ 1 f x‖ ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x ∂(m.tilted (-V)) = 0 := by
  have hC : 0 ≤ C := by
    have h := (hfg 0).1
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hCV : 0 ≤ CV := by
    have h := hVg 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (norm_nonneg _).trans h
  obtain ⟨C₁, h₁⟩ := FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_cutoff_le_readable (E := E) 1
  obtain ⟨C₂, h₂⟩ := FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_cutoff_le_readable (E := E) 2
  let K : ℝ := |C₁| + |C₂|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcut (R : ℝ) (hR : 1 ≤ R) (x : E) :
      ‖iteratedFDeriv ℝ 1 (FunctionalInequalities.Analysis.BakryEmery.cutoff R) x‖ ≤ K ∧
        ‖iteratedFDeriv ℝ 2 (FunctionalInequalities.Analysis.BakryEmery.cutoff R) x‖ ≤ K := by
    constructor
    · exact (h₁ R hR x).trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
    · exact (h₂ R hR x).trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))
  let A : ℝ := (Module.finrank ℝ E : ℝ) * C + CV * C
  let B : ℝ := (Module.finrank ℝ E : ℝ) * K + CV * K
  let H : ℝ := A + 2 * K * C + C * B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hLf (x : E) :
      |FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x| ≤ A * (1 + ‖x‖) ^ (k + kV) :=
    FunctionalInequalities.Analysis.BakryEmery.growth_weightedLaplacian_bound hCV hC hVg (fun x => (hfg x).2) x
  have hLcut (R : ℝ) (hR : 1 ≤ R) (x : E) :
      |FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V (FunctionalInequalities.Analysis.BakryEmery.cutoff R) x| ≤ B * (1 + ‖x‖) ^ kV := by
    simpa only [pow_zero, mul_one, zero_add] using
      FunctionalInequalities.Analysis.BakryEmery.growth_weightedLaplacian_bound hCV hK hVg
        (g := FunctionalInequalities.Analysis.BakryEmery.cutoff R) (k := 0) (fun y => by simpa using hcut R hR y) x
  let F : ℕ → E → ℝ := fun n =>
    FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V (fun x => FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x * f x)
  have hbound (n : ℕ) (x : E) :
      ‖F n x‖ ≤ H * (1 + ‖x‖) ^ (k + kV) := by
    have hR : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hc : ContDiff ℝ 2 (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) : E → ℝ) :=
      (FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff (E := E) ((n : ℝ) + 1)).of_le
        (show (2 : ℕ∞ω) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)
    have hgcut : ‖gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ ≤ K := by
      rw [FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one]
      exact (hcut _ hR x).1
    have hgf : ‖gradient f x‖ ≤ C * (1 + ‖x‖) ^ k := by
      rw [FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one]
      exact (hfg x).2.1
    have hp : 1 ≤ (1 + ‖x‖) ^ kV := one_le_pow₀ (by linarith [norm_nonneg x])
    have hp' : (1 + ‖x‖) ^ k ≤ (1 + ‖x‖) ^ (k + kV) := by
      rw [pow_add]
      exact le_mul_of_one_le_right (by positivity) hp
    dsimp only [F]
    rw [Real.norm_eq_abs, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_mul V hc hf x, FunctionalInequalities.Analysis.BakryEmery.gamma_apply]
    rw [show ∀ a b c : ℝ, a + b + 2 * c = a + 2 * c + b from fun a b c => by ring]
    calc
      |FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x +
          2 * ⟪gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x, gradient f x⟫ +
          f x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x| ≤
          |FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x| * |FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x| +
            2 * (‖gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ * ‖gradient f x‖) +
            |f x| * |FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x| := by
        calc
          _ ≤ |FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x| +
              |2 * ⟪gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x, gradient f x⟫| +
              |f x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x| :=
            (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
          _ ≤ _ := by
            simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
            gcongr
            exact abs_real_inner_le_norm _ _
      _ ≤ 1 * (A * (1 + ‖x‖) ^ (k + kV)) +
            2 * (K * (C * (1 + ‖x‖) ^ k)) +
            (C * (1 + ‖x‖) ^ k) * (B * (1 + ‖x‖) ^ kV) := by
        gcongr
        · exact FunctionalInequalities.Analysis.BakryEmery.abs_cutoff_le_one _ _
        · exact hLf x
        · exact (hfg x).1
        · exact hLcut _ hR x
      _ ≤ 1 * (A * (1 + ‖x‖) ^ (k + kV)) +
            2 * (K * (C * (1 + ‖x‖) ^ (k + kV))) +
            (C * (1 + ‖x‖) ^ k) * (B * (1 + ‖x‖) ^ kV) := by
        exact add_le_add_left (add_le_add_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp' hC) hK)
          (by norm_num)) _) _
      _ = H * (1 + ‖x‖) ^ (k + kV) := by dsimp [H]; rw [pow_add]; ring
  have hbi : Integrable (fun x : E => H * (1 + ‖x‖) ^ (k + kV))
      (m.tilted (-V)) := by
    apply FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_readable _ hexp (by fun_prop) (C := H) (k := k + kV)
    intro x
    rw [Real.norm_of_nonneg (by positivity)]
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) (m.tilted (-V)) :=
    (FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian hV
      (((FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff (E := E) ((n : ℝ) + 1)).of_le
        (show (2 : ℕ∞ω) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)).mul hf)).aestronglyMeasurable
  have hlim (x : E) : Tendsto (fun n => F n x) atTop (𝓝 (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x)) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hx : ‖x‖ < (n : ℝ) + 1 := by linarith
    symm
    apply FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_congr_of_eventuallyEq V
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    rw [FunctionalInequalities.Analysis.BakryEmery.cutoff_eq_one_readable (by positivity) hy.le, one_mul]
  have ht := tendsto_integral_of_dominated_convergence
    (fun x : E => H * (1 + ‖x‖) ^ (k + kV)) hmeas hbi
    (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hlim)
  have hz (n : ℕ) : (∫ x, F n x ∂(m.tilted (-V))) = 0 :=
    FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero m hV
      (((FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff (E := E) ((n : ℝ) + 1)).of_le
        (show (2 : ℕ∞ω) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)).mul hf)
      ((FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_cutoff_readable (by positivity)).mul_right)
  simp_rw [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds
