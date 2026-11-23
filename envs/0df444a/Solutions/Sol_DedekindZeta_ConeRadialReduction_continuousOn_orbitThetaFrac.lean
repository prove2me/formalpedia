-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.continuousOn_orbitThetaFrac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:49:12.354209+00:00
-- url     : https://prove2.me/submissions/00e276a7-837e-4011-b100-453f7d3a71ac

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measurableSet_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap_of_mem
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuous_radialMap_uncurry
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_eq_exp_quadForm
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_nonneg
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedQuadForm_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_integrableOn_mixedThetaKernel_radialMap
import Theorems.Thm_DedekindZeta_Theta_continuousOn_mixedThetaKernel
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_summable_mixedGaussian_submodule
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) :
    ContinuousOn (orbitThetaFrac K I) (Set.Ioi 0) := by
  classical
  -- The zero ideal: the kernel sums over the empty index set, so `orbitThetaFrac ≡ 0`.
  by_cases hI : I = 0
  · have hzero : orbitThetaFrac K I = fun _ : ℝ => (0 : ℂ) := by
      funext r
      rw [orbitThetaFrac]
      have hker : ∀ σ : mixedSpace K,
          Theta.mixedThetaKernel K I (radialMap K r σ) = 0 := by
        intro σ
        subst hI
        haveI : IsEmpty {a : K // a ∈ ((0 : FractionalIdeal (𝓞 K)⁰ K) :
            Submodule (𝓞 K) K) ∧ a ≠ 0} := by
          refine ⟨?_⟩
          rintro ⟨a, ha, ha0⟩
          rw [FractionalIdeal.coe_zero, Submodule.mem_bot] at ha
          exact ha0 ha
        rw [Theta.mixedThetaKernel, tsum_empty]
      simp only [hker, integral_zero]
    rw [hzero]
    exact continuousOn_const
  -- Nonzero ideal: dominated continuity of the parametric integral over the
  -- (finite-measure) norm-1 surface slice.
  set μ : Measure (mixedSpace K) := (surfaceMeasure K).restrict (normEqOneSurface K)
    with hμ
  -- Summability of the real Gaussian family over the nonzero elements of `I`,
  -- at any nonzero-norm point `y` (subfamily of `summable_mixedGaussian_submodule`).
  set T := {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} with hT
  have hsummable : ∀ y : mixedSpace K, mixedEmbedding.norm y ≠ 0 →
      Summable (fun a : T => Theta.mixedGaussian K (y * mixedEmbedding K (a : K))) := by
    intro y hy
    have hinc_inj : Function.Injective
        (fun a : T => (⟨a.1, a.2.1⟩ : (I : Submodule (𝓞 K) K))) := by
      intro a b h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
    have hcomp := (Theta.summable_mixedGaussian_submodule K I hI hy).comp_injective hinc_inj
    rw [← Complex.summable_ofReal]
    exact hcomp.congr (fun a => rfl)
  -- `‖kernel x‖` equals the real lattice Gaussian sum at any nonzero-norm `x`.
  have hnorm_eq : ∀ {x : mixedSpace K}, mixedEmbedding.norm x ≠ 0 →
      ‖Theta.mixedThetaKernel K I x‖
        = ∑' a : T, Theta.mixedGaussian K (x * mixedEmbedding K (a : K)) := by
    intro x _hx
    rw [Theta.mixedThetaKernel, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg (fun a => mixedGaussian_nonneg _))]
  refine continuousOn_of_forall_continuousAt (fun r₀ hr₀ => ?_)
  have hr₀0 : (0 : ℝ) < r₀ := hr₀
  set rlo : ℝ := r₀ / 2 with hrlo
  have hlo0 : (0 : ℝ) < rlo := by rw [hrlo]; linarith
  have hlt : rlo < r₀ := by rw [hrlo]; linarith
  -- The dominating function `g σ = ‖kernel (radialMap K rlo σ)‖`, integrable on `S`.
  have hint_lo : IntegrableOn
      (fun σ => Theta.mixedThetaKernel K I (radialMap K rlo σ))
      (normEqOneSurface K) (surfaceMeasure K) :=
    integrableOn_mixedThetaKernel_radialMap (K := K) I rlo hlo0
  have hbound_int :
      Integrable (fun σ => ‖Theta.mixedThetaKernel K I (radialMap K rlo σ)‖) μ :=
    hint_lo.norm
  -- Per-radius monotone domination for `r ≥ rlo` over the surface.
  have hdom : ∀ x : ℝ, rlo ≤ x → ∀ σ ∈ normEqOneSurface K,
      ‖Theta.mixedThetaKernel K I (radialMap K x σ)‖
        ≤ ‖Theta.mixedThetaKernel K I (radialMap K rlo σ)‖ := by
    intro x hx σ hσ
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hlo0 hx
    have hxnorm : mixedEmbedding.norm (radialMap K x σ) ≠ 0 := by
      rw [norm_radialMap_of_mem x hx0 hσ]; exact hx0.ne'
    have hlonorm : mixedEmbedding.norm (radialMap K rlo σ) ≠ 0 := by
      rw [norm_radialMap_of_mem rlo hlo0 hσ]; exact hlo0.ne'
    rw [hnorm_eq hxnorm, hnorm_eq hlonorm]
    refine Summable.tsum_le_tsum (fun a => ?_)
      (hsummable _ hxnorm) (hsummable _ hlonorm)
    have hmulx : radialMap K x σ * mixedEmbedding K (a : K)
        = radialMap K x (σ * mixedEmbedding K (a : K)) := by
      rw [radialMap, radialMap, smul_mul_assoc]
    have hmullo : radialMap K rlo σ * mixedEmbedding K (a : K)
        = radialMap K rlo (σ * mixedEmbedding K (a : K)) := by
      rw [radialMap, radialMap, smul_mul_assoc]
    rw [hmulx, hmullo, mixedGaussian_eq_exp_quadForm, mixedGaussian_eq_exp_quadForm,
      mixedQuadForm_radialMap x hx0, mixedQuadForm_radialMap rlo hlo0]
    refine Real.exp_le_exp.mpr ?_
    set Q : ℝ := mixedQuadForm K (σ * mixedEmbedding K (a : K)) with hQ
    have hQ0 : 0 ≤ Q := by
      rw [hQ, mixedQuadForm]
      exact Finset.sum_nonneg (fun w _ => by positivity)
    have hexp : (0 : ℝ) ≤ 2 * (finrank ℚ K : ℝ)⁻¹ := by positivity
    have hrpow : rlo ^ (2 * (finrank ℚ K : ℝ)⁻¹) ≤ x ^ (2 * (finrank ℚ K : ℝ)⁻¹) :=
      Real.rpow_le_rpow hlo0.le hx hexp
    have hπ := Real.pi_pos
    nlinarith [mul_nonneg (mul_nonneg hπ.le (sub_nonneg.mpr hrpow)) hQ0]
  -- Assemble the four hypotheses of `continuousAt_of_dominated`.
  have hmeas : ∀ x ∈ Set.Ioi rlo,
      AEStronglyMeasurable (fun σ => Theta.mixedThetaKernel K I (radialMap K x σ)) μ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hlo0 hx
    exact (integrableOn_mixedThetaKernel_radialMap (K := K) I x hx0).aestronglyMeasurable
  have hF_meas : ∀ᶠ x in nhds r₀,
      AEStronglyMeasurable (fun σ => Theta.mixedThetaKernel K I (radialMap K x σ)) μ :=
    Filter.eventually_of_mem (Ioi_mem_nhds hlt) hmeas
  have hbound : ∀ᶠ x in nhds r₀, ∀ᵐ σ ∂μ,
      ‖Theta.mixedThetaKernel K I (radialMap K x σ)‖
        ≤ ‖Theta.mixedThetaKernel K I (radialMap K rlo σ)‖ := by
    refine Filter.eventually_of_mem (Ioi_mem_nhds hlt) (fun x hx => ?_)
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_normEqOneSurface).mpr ?_
    exact Filter.Eventually.of_forall (fun σ hσ => hdom x (le_of_lt hx) σ hσ)
  have hcont : ∀ᵐ σ ∂μ,
      ContinuousAt (fun x => Theta.mixedThetaKernel K I (radialMap K x σ)) r₀ := by
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_normEqOneSurface).mpr ?_
    refine Filter.Eventually.of_forall (fun σ hσ => ?_)
    have hr₀norm : mixedEmbedding.norm (radialMap K r₀ σ) ≠ 0 := by
      rw [norm_radialMap_of_mem r₀ hr₀0 hσ]; exact hr₀0.ne'
    have hUopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
      isOpen_ne.preimage (mixedEmbedding.continuous_norm K)
    have houter : ContinuousAt (Theta.mixedThetaKernel K I) (radialMap K r₀ σ) :=
      (Theta.continuousOn_mixedThetaKernel K I).continuousAt (hUopen.mem_nhds hr₀norm)
    have hinner : ContinuousAt (fun x : ℝ => radialMap K x σ) r₀ := by
      have hc : Continuous (fun x : ℝ => radialMap K x σ) :=
        continuous_radialMap_uncurry.comp (Continuous.prodMk continuous_id continuous_const)
      exact hc.continuousAt
    exact houter.comp_of_eq hinner rfl
  have hrw : orbitThetaFrac K I
      = fun x => ∫ σ, Theta.mixedThetaKernel K I (radialMap K x σ) ∂μ := by
    funext x; rw [orbitThetaFrac, hμ]
  rw [hrw]
  exact continuousAt_of_dominated hF_meas hbound hbound_int hcont
end DedekindZeta.ConeRadialReduction
