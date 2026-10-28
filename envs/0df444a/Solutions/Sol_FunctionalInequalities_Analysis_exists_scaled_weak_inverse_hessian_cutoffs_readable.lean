-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_scaled_weak_inverse_hessian_cutoffs_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:14:57.551103+00:00
-- url     : https://prove2.me/submissions/fe6315d4-7c1f-464a-b774-dde4b966132c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff
import Theorems.Thm_FunctionalInequalities_Analysis_deriv_comp_sub_div_and_deriv_deriv_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_readable
import Theorems.Thm_FunctionalInequalities_Analysis_inv_mul_intervalIntegral_div_three_cutoff_readable
import Theorems.Thm_FunctionalInequalities_Analysis_monotoneOn_and_tendsto_smoothTransition_two_sub_div_readable
import Theorems.Thm_FunctionalInequalities_Analysis_smoothTransition_two_sub_cutoff_readable
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_exists_lipschitzWith_smul_of_locallyLipschitz_readable
import Theorems.Thm_FunctionalInequalities_Analysis_ae_hessianMatrix_comp_profile_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_C1_height_generator_defect_bound_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_profile_inverse_energy_eq_drift_readable

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
/-- Chain rule for the gradient: `∇(Φ ∘ g) = Φ'(g) ∇g`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_comp {Φ : ℝ → ℝ} {g : E → ℝ} {x : E} (hΦ : DifferentiableAt ℝ Φ (g x))
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => Φ (g y)) x = deriv Φ (g x) • gradient g x := by
  have hcomp : HasFDerivAt (fun y => Φ (g y)) (deriv Φ (g x) • fderiv ℝ g x) x :=
    hΦ.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt
  unfold gradient
  rw [hcomp.fderiv, map_smul]
end Gradient
end DifferentialTools
end
end
end

section
noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
section
/-- A unit normalisation `∫ e^{−φ} = 1` forces integrability of `e^{−φ}`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integrable_exp_neg_of_integral_eq_one {α : Type*} [MeasurableSpace α] (m : Measure α)
    (φ : α → ℝ) (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    Integrable (fun x => Real.exp (-φ x)) m := by
  by_contra hh
  rw [integral_undef hh] at hnorm
  norm_num at hnorm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end
end
end

noncomputable section
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace
private theorem FunctionalInequalities.Analysis.integrable_profile_energy_and_integral_le {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport (fun x => ζ (u x)))
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {D B : ℝ} (hD : 0 ≤ D)
    (hζbound : ∀ x, 0 ≤ ζ (u x) ∧ ζ (u x) ≤ B)
    (hdrift : ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D) :
    Integrable (fun x =>
      -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ D * B := by
  have hp := integral_profile_inverse_energy_eq_drift_readable hu hG hV hF hdet hζ hζc
  have hc : Continuous (fun x => (n : ℝ) -
      fderiv ℝ V (gradient u x) (gradient u x)) :=
    continuous_const.sub
      (((hV.continuous_fderiv one_ne_zero).comp hG.continuous).clm_apply hG.continuous)
  have hi : Integrable (fun x => ζ (u x) *
      ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (((hζ.continuous.comp hu.continuous).mul hc).mul
      (Real.continuous_exp.comp hu.continuous.neg)).integrable_of_hasCompactSupport
        hζc.mul_right.mul_right
  have hexp := BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) * Real.exp (-u x) ≤
        (D * B) * Real.exp (-u x) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      _ ≤ ζ (u x) * D := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hdrift x)) (hζbound x).1
      _ ≤ B * D := mul_le_mul_of_nonneg_right (hζbound x).2 hD
      _ = _ := mul_comm _ _
  refine ⟨hp.1.neg.congr (Filter.Eventually.of_forall fun x => by
    change -(_ * _) = -_ * _
    ring), ?_⟩
  calc
    _ = _ := hp.2
    _ ≤ ∫ x, (D * B) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      integral_mono hi (hexp.const_mul (D * B)) hpoint
    _ = D * B := by rw [integral_const_mul, hnorm, mul_one]
private theorem FunctionalInequalities.Analysis.hasCompactSupport_comp_of_isCompact_sublevel {E : Type*} [TopologicalSpace E] {φ : E → ℝ} {g : ℝ → ℝ} {T : ℝ}
    (hφ : Continuous φ) (hsub : IsCompact {y | φ y ≤ T}) (hg : ∀ s, T ≤ s → g s = 0) :
    HasCompactSupport (fun x => g (φ x)) := by
    refine HasCompactSupport.intro' hsub (isClosed_le hφ continuous_const) ?_
    intro x hx
    have hx' : ¬ φ x ≤ T := hx
    exact hg (φ x) (le_of_lt (lt_of_not_ge hx'))
private theorem FunctionalInequalities.Analysis.shifted_inv_mul_intervalIntegral_div_three_cutoff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hw0 : ∀ t, 0 ≤ w t) (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) (c : ℝ) :
    ContDiff ℝ ∞ (fun s => R⁻¹ * ∫ t in (s - c) / R..3, w t) ∧
      (∀ s, deriv (fun s => R⁻¹ * ∫ t in (s - c) / R..3, w t) s = -((R ^ 2)⁻¹ * w ((s - c) / R))) ∧
      (∀ s, |R⁻¹ * ∫ t in (s - c) / R..3, w t| ≤ R⁻¹ * ∫ t in (0 : ℝ)..3, w t) ∧
      (∀ s, c + 3 * R ≤ s → R⁻¹ * ∫ t in (s - c) / R..3, w t = 0) := by
    obtain ⟨hq, hqd, hq0, hqBound, hqZero⟩ :=
      inv_mul_intervalIntegral_div_three_cutoff_readable hw hw0 hws hR
    let q : ℝ → ℝ := fun t => R⁻¹ * ∫ u in t / R..3, w u
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hq.comp (contDiff_id.sub contDiff_const)
    · intro s
      have hshift :
          deriv (fun t => q (t - c)) s = deriv q (s - c) := by
        simpa only [div_one, inv_one, one_mul] using
          (deriv_comp_sub_div_and_deriv_deriv_readable q c 1 s).1
      calc
        deriv (fun t => R⁻¹ * ∫ u in (t - c) / R..3, w u) s =
            deriv q (s - c) := hshift
        _ = -((R ^ 2)⁻¹ * w ((s - c) / R)) := hqd (s - c)
    · intro s
      rw [abs_of_nonneg (hq0 (s - c))]
      exact hqBound (s - c)
    · intro s hs
      exact hqZero (s - c) (by linarith)
private theorem FunctionalInequalities.Analysis.integrable_majorant_inverse_energy_and_integral_le {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hsub : ∀ t : ℝ, IsCompact {x | u x ≤ t}) {D : ℝ} (hD : 0 ≤ D)
    (hdrift : ∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hw0 : ∀ t, 0 ≤ w t)
    (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) (c : ℝ) :
    Integrable (fun x => (R ^ 2)⁻¹ * w ((u x - c) / R) *
      (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, (R ^ 2)⁻¹ * w ((u x - c) / R) *
      (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        D * (R⁻¹ * ∫ t in (0 : ℝ)..3, w t) := by
  let ζ : ℝ → ℝ := fun s => R⁻¹ * ∫ t in (s - c) / R..3, w t
  obtain ⟨hζ, hζd, hζbound, hζzero⟩ :=
    shifted_inv_mul_intervalIntegral_div_three_cutoff hw hw0 hws hR c
  have hζc : HasCompactSupport (fun x => ζ (u x)) :=
    hasCompactSupport_comp_of_isCompact_sublevel hu.continuous (hsub (c + 3 * R)) hζzero
  obtain ⟨_hq, _hqd, hq0, _hqb, _hqz⟩ :=
    inv_mul_intervalIntegral_div_three_cutoff_readable hw hw0 hws hR
  have hp := integrable_profile_energy_and_integral_le hu hG hV hF hdet
    (hζ.of_le (WithTop.coe_le_coe.mpr le_top)) hζc hnorm hD
    (fun x => ⟨hq0 (u x - c), (le_abs_self _).trans (hζbound (u x))⟩) hdrift
  have heq (x : EuclideanSpace ℝ (Fin n)) :
      -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x) =
      (R ^ 2)⁻¹ * w ((u x - c) / R) *
        (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x) := by
    rw [show deriv ζ (u x) = -((R ^ 2)⁻¹ * w ((u x - c) / R)) from hζd (u x)]
    ring
  refine ⟨hp.1.congr (Filter.Eventually.of_forall heq), ?_⟩
  exact (integral_congr_ae (Filter.Eventually.of_forall fun x => (heq x).symm)).le.trans hp.2
private theorem FunctionalInequalities.Analysis.contDiff_one_and_exists_lipschitz_gradient_comp_profile {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hζ : ContDiff ℝ 2 ζ)
    (hc : HasCompactSupport (fun x => deriv ζ (u x))) :
    ContDiff ℝ 1 (fun x => ζ (u x)) ∧
      ∃ K : NNReal, LipschitzWith K (gradient (fun x => ζ (u x))) := by
  have hζd : ContDiff ℝ 1 (deriv ζ) := hζ.deriv'
  have hcoeff : ContDiff ℝ 1 (fun x => deriv ζ (u x)) := hζd.comp hu
  obtain ⟨Kc, hKc⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hcoeff one_ne_zero
  obtain ⟨⟨K, hK⟩, _⟩ :=
    FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz_readable
      hKc hc hG.locallyLipschitz
  refine ⟨(hζ.of_le one_le_two).comp hu, K, ?_⟩
  have heq : gradient (fun x => ζ (u x)) = fun x => deriv ζ (u x) • gradient u x := by
    funext x
    exact BakryEmery.gradient_comp
      ((hζ.differentiable (by norm_num)).differentiableAt)
      ((hu.differentiable one_ne_zero).differentiableAt)
  rw [heq]
  exact hK
private theorem FunctionalInequalities.Analysis.scaled_C1_height_cutoff_family {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hsub : ∀ t : ℝ, IsCompact {x | u x ≤ t}) (c : ℝ) :
    let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
    (∀ R : ℝ, 1 ≤ R →
      ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
      (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
      HasCompactSupport
        (fun x => deriv (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R)) (u x)) ∧
      ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
    (∀ x, MonotoneOn (fun R => χ R x) (Set.Ici 1)) ∧
    ∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1) := by
  let η : ℝ → ℝ := fun s => Real.smoothTransition (2 - s)
  let ζ : ℝ → ℝ → ℝ := fun R s => η ((s - c) / R)
  obtain ⟨hη, _hηanti, hηbounds, _hηone, hηzero, hηderiv,
    _hηsupp, _hηsupp₂, _B, _hB0, _hB⟩ := smoothTransition_two_sub_cutoff_readable
  have hζ (R : ℝ) : ContDiff ℝ ∞ (ζ R) :=
    hη.comp ((contDiff_id.sub contDiff_const).div_const R)
  refine ⟨?_, ?_, ?_⟩
  · intro R hR
    have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hχc : HasCompactSupport (fun x => ζ R (u x)) := by
      apply hasCompactSupport_comp_of_isCompact_sublevel hu.continuous (hsub (c + 2 * R))
      intro s hs
      apply hηzero
      apply (le_div_iff₀ hRp).2
      linarith
    have hcoeff : HasCompactSupport (fun x => deriv (ζ R) (u x)) := by
      apply hasCompactSupport_comp_of_isCompact_sublevel hu.continuous (hsub (c + 3 * R))
      intro s hs
      change deriv (fun t => η ((t - c) / R)) s = 0
      rw [(deriv_comp_sub_div_and_deriv_deriv_readable η c R s).1]
      have ht : 2 < (s - c) / R := by
        apply (lt_div_iff₀ hRp).2
        nlinarith
      rw [(hηderiv ((s - c) / R) (Or.inr ht)).1, mul_zero]
    have hreg := contDiff_one_and_exists_lipschitz_gradient_comp_profile hu hG
      ((hζ R).of_le (WithTop.coe_le_coe.mpr le_top)) hcoeff
    exact ⟨hreg.1, hχc, hreg.2, hcoeff, fun x => hηbounds ((u x - c) / R)⟩
  · intro x
    exact (monotoneOn_and_tendsto_smoothTransition_two_sub_div_readable (u x - c)).1.mono
      (fun R hR => show (0 : ℝ) < R from lt_of_lt_of_le zero_lt_one hR)
  · intro x
    exact (monotoneOn_and_tendsto_smoothTransition_two_sub_div_readable (u x - c)).2
private theorem FunctionalInequalities.Analysis.trace_mul_of_profile_entries {n : ℕ}
    (R H K : Matrix (Fin n) (Fin n) ℝ) (α β : ℝ) (v : Fin n → ℝ)
    (hK : ∀ i j, K i j = α * H i j + β * v i * v j) :
    (R * K).trace = α * (R * H).trace +
      β * (∑ i : Fin n, ∑ j : Fin n, R i j * v i * v j) := by
  have hentry (i j : Fin n) : R i j * K j i =
      α * (R i j * H j i) + β * (R i j * v i * v j) := by
    rw [hK j i]
    ring
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hentry,
    Finset.sum_add_distrib, ← Finset.mul_sum]
private theorem FunctionalInequalities.Analysis.ae_inverse_hessian_generator_comp_profile {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hζ : ContDiff ℝ 2 ζ)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det ≠ 0)
    (V : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((hessianMatrix u x)⁻¹ * hessianMatrix (fun y => ζ (u y)) x).trace -
          fderiv ℝ V (gradient u x) (gradient (fun y => ζ (u y)) x) =
        deriv ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) +
          deriv (deriv ζ) (u x) *
            (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
              fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
              fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  filter_upwards [ae_hessianMatrix_comp_profile_readable hu hG hζ, hdet] with x hc hd
  have htrace := trace_mul_of_profile_entries (hessianMatrix u x)⁻¹
    (hessianMatrix u x) (hessianMatrix (fun y => ζ (u y)) x)
    (deriv ζ (u x)) (deriv (deriv ζ) (u x))
    (fun i => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i)) hc
  have hRH : (hessianMatrix u x)⁻¹ * hessianMatrix u x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd)
  have hgrad : gradient (fun y => ζ (u y)) x = deriv ζ (u x) • gradient u x :=
    BakryEmery.gradient_comp ((hζ.differentiable (by norm_num)).differentiableAt)
      ((hu.differentiable one_ne_zero).differentiableAt)
  rw [htrace, hRH, hgrad, map_smul]
  simp only [Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  ring
private theorem FunctionalInequalities.Analysis.exists_bound_moment_gradient_drift {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hL : LipschitzWith L u) (hV : ContDiff ℝ 1 V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x,
      |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D := by
  have hDV : Continuous (fderiv ℝ V) := hV.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ)).exists_bound_of_continuousOn
    hDV.continuousOn
  have hgrad (x : EuclideanSpace ℝ (Fin n)) : ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hL)
  refine ⟨(n : ℝ) + max M 0 * (L : ℝ),
    add_nonneg (Nat.cast_nonneg n) (mul_nonneg (le_max_right _ _) L.coe_nonneg), ?_⟩
  intro x
  have hx : gradient u x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hgrad x
  have hnorm : ‖fderiv ℝ V (gradient u x) (gradient u x)‖ ≤ max M 0 * (L : ℝ) :=
    ((fderiv ℝ V (gradient u x)).le_opNorm (gradient u x)).trans
      (mul_le_mul ((hM _ hx).trans (le_max_left _ _)) (hgrad x)
        (norm_nonneg _) (le_max_right _ _))
  calc
    _ ≤ ‖(n : ℝ)‖ + ‖fderiv ℝ V (gradient u x) (gradient u x)‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_sub_le (n : ℝ) (fderiv ℝ V (gradient u x) (gradient u x))
    _ ≤ _ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
      linarith [hnorm]
private theorem FunctionalInequalities.Analysis.sum_inverse_quadratic_nonneg_of_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, A⁻¹ i j * v i * v j := by
  calc
    0 ≤ star v ⬝ᵥ (A⁻¹ *ᵥ v) := hA.inv.posSemidef.dotProduct_mulVec_nonneg v
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
private theorem FunctionalInequalities.Analysis.exists_C1_height_cutoff_generator_majorant_data {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
    (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1) :
    ∃ c D : ℝ, 0 ≤ D ∧ (∀ x, 1 ≤ u x - c) ∧
      (∀ t : ℝ, IsCompact {x | u x ≤ t}) ∧
      (∀ x, |(n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)| ≤ D) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Γ := fun x => ∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        HasCompactSupport
          (fun x => deriv (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R)) (u x)) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ Γ x) ∧
      (∀ R : ℝ, 1 ≤ R →
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
            fderiv ℝ V (gradient u x) (gradient (χ R) x) =
          deriv (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R)) (u x) *
            ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) +
          deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R))) (u x) * Γ x) ∧
      ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → (∀ t, 0 ≤ w t) →
        (∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) → ∀ R : ℝ, 0 < R →
        Integrable (fun x => (R ^ 2)⁻¹ * w ((u x - c) / R) * Γ x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (R ^ 2)⁻¹ * w ((u x - c) / R) * Γ x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            D * (R⁻¹ * ∫ t in (0 : ℝ)..3, w t) := by
  obtain ⟨⟨y₀, hy₀⟩, hsub⟩ :=
    exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_readable
      (volume : Measure (EuclideanSpace ℝ (Fin n))) hconv
      (BakryEmery.integrable_exp_neg_of_integral_eq_one
        (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm)
  let c : ℝ := u y₀ - 1
  have hshift (x : EuclideanSpace ℝ (Fin n)) : 1 ≤ u x - c := by
    dsimp only [c]
    linarith [hy₀ x]
  obtain ⟨D, hD, hdrift⟩ := exists_bound_moment_gradient_drift hL hV
  obtain ⟨hχ, hmono, hlim⟩ := scaled_C1_height_cutoff_family hu hG hsub c
  refine ⟨c, D, hD, hshift, hsub, hdrift, ?_⟩
  dsimp only
  refine ⟨hχ, hmono, hlim, ?_, ?_, ?_⟩
  · filter_upwards [hPD] with x hx
    exact sum_inverse_quadratic_nonneg_of_posDef (hessianMatrix u x) hx
      (fun i => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i))
  · intro R _hR
    obtain ⟨hη, _⟩ := smoothTransition_two_sub_cutoff_readable
    have hζ : ContDiff ℝ 2 (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R)) :=
      (hη.comp ((contDiff_id.sub contDiff_const).div_const R)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    exact ae_inverse_hessian_generator_comp_profile hu hG hζ
      (hdet.mono fun x hx => hx.trans_ne (Real.exp_ne_zero _)) V
  · intro w hw hw0 hws R hR
    exact integrable_majorant_inverse_energy_and_integral_le hu hG hV hF hdet
      hnorm hsub hD hdrift hw hw0 hws hR c
/-- The real-parameter weak C1 inverse-Hessian height cutoffs, with vanishing generator defect. -/
theorem solution {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef)
    (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1) :
    ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix (χ R) x).trace -
        fderiv ℝ V (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) := by
  obtain ⟨c, D, hD, hshift, hsub, hdrift, hχ, hmono, hlim, _hΓ, _hgen, _hmajor⟩ :=
    FunctionalInequalities.Analysis.exists_C1_height_cutoff_generator_majorant_data hu hL hG hV hF hdet hPD hconv hnorm
  obtain ⟨C, hC, hcore⟩ := FunctionalInequalities.Analysis.exists_C1_height_generator_defect_bound_readable
    hu hG hV hF hdet hPD hnorm hsub hD hdrift c
  let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
  let Lχ := fun R x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix (χ R) x).trace -
    fderiv ℝ V (gradient u x) (gradient (χ R) x)
  have hexp := FunctionalInequalities.Analysis.BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm
  have hweighted (R : ℝ) (hR : 1 ≤ R) :
      Integrable (fun x => Lχ R x * Real.exp (-u x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, |Lχ R x| * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ C / R := hcore R hR
  have hint (R : ℝ) (hR : 1 ≤ R) : Integrable (Lχ R)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
    apply (integrable_tilted_iff hexp (Lχ R)).mpr
    simpa only [Pi.neg_apply, smul_eq_mul, mul_comm] using (hweighted R hR).1
  have heq (R : ℝ) :
      (∫ x, |Lχ R x| ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ x, |Lχ R x| * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [integral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hbound (R : ℝ) (hR : 1 ≤ R) :
      (∫ x, |Lχ R x| ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R := by
    rw [heq]
    exact (hweighted R hR).2
  have hdecay : Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) := by
    have hCdiv : Tendsto (fun R : ℝ => C / R) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).const_mul C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCdiv
    · exact Filter.Eventually.of_forall fun R => integral_nonneg fun x => abs_nonneg _
    · exact Filter.eventually_atTop.mpr ⟨1, fun R hR => hbound R hR⟩
  refine ⟨c, C, hC, hshift, ?_, hmono, hlim, hint, hbound, hdecay⟩
  intro R hR
  obtain ⟨hC1, hcomp, hLip, _hderiv, hRange⟩ := hχ R hR
  exact ⟨hC1, hcomp, hLip, hRange⟩
