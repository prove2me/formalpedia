-- Prove2me | solution 1 for DedekindZeta.Theta.mixedThetaKernel_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:30:54.981799+00:00
-- url     : https://prove2.me/submissions/107d81bf-d775-4cf6-9015-b2f06a932062

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_dualLattice_idealLattice
import Theorems.Thm_DedekindZeta_Theta_discreteTopology_idealLattice
import Theorems.Thm_DedekindZeta_Theta_isZLattice_idealLattice
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_covolume_idealLattice
import Theorems.Thm_DedekindZeta_Theta_fourier_mixedGaussian_scaling
import Theorems.Thm_DedekindZeta_Theta_mixedGaussian_mul_conjMixed
import Theorems.Thm_DedekindZeta_Theta_tsum_mixedGaussian_submodule
import Theorems.Thm_DedekindZeta_PoissonSummation_tsum_eq_tsum_fourier

attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    (x : mixedEmbedding.mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    mixedThetaKernel K (𝔞 : FractionalIdeal (𝓞 K)⁰ K) x⁻¹ =
      ((|mixedEmbedding.norm x| / covolume K 𝔞 : ℝ) : ℂ) *
        (mixedThetaKernel K (dualIdeal K 𝔞) x + 1) - 1 := by
  classical
  set I : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hIdef
  have hI : I ≠ 0 := by rw [hIdef]; exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr hne
  -- The dual ideal is nonzero (inverse of a nonzero fractional ideal).
  have hdiff : differentFractionalIdeal K ≠ 0 := by
    rw [differentFractionalIdeal]
    exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr differentIdeal_ne_bot
  have hD : dualIdeal K 𝔞 ≠ 0 := by
    rw [dualIdeal]
    exact inv_ne_zero (mul_ne_zero (by rw [← hIdef]; exact hI) hdiff)
  -- Inverse-scaling facts: `N(x⁻¹) ≠ 0` and `|N(x⁻¹)|⁻¹ = |N(x)|`.
  have hxx : x * x⁻¹ = 1 := mul_inv_cancel_of_norm_ne_zero K hx
  have hN1 : mixedEmbedding.norm x * mixedEmbedding.norm x⁻¹ = 1 := by
    rw [← map_mul, hxx, map_one]
  have hxinv : mixedEmbedding.norm x⁻¹ ≠ 0 := by
    intro h; rw [h, mul_zero] at hN1; exact one_ne_zero hN1.symm
  have hb : mixedEmbedding.norm x⁻¹ = (mixedEmbedding.norm x)⁻¹ :=
    eq_inv_of_mul_eq_one_right hN1
  have hAbs : |mixedEmbedding.norm x⁻¹|⁻¹ = |mixedEmbedding.norm x| := by
    rw [hb, abs_inv, inv_inv]
  -- Lattice instances on `Λ(𝔞)`.
  haveI := discreteTopology_idealLattice K I hI
  haveI := isZLattice_idealLattice K I hI
  -- Lattice Poisson summation for the scaled Gaussian Schwartz function.
  have hPoisson := PoissonSummation.tsum_eq_tsum_fourier (idealLattice K I)
    (mixedGaussianSchwartz K hxinv)
  -- Primal side: `∑_{v ∈ Λ(𝔞)} g(x⁻¹·σ⁻¹ v) = 1 + Θ(𝔞, x⁻¹)`.
  have hprimal : ∑' v : idealLattice K I,
        (mixedGaussianSchwartz K hxinv : minkowskiSpace K → ℂ) v
      = 1 + mixedThetaKernel K I x⁻¹ := by
    rw [← tsum_mixedGaussian_submodule K I hI hxinv,
      ← Equiv.tsum_eq (idealLatticeEquiv K I)
        (fun v : idealLattice K I => (mixedGaussianSchwartz K hxinv : minkowskiSpace K → ℂ) v)]
    refine tsum_congr (fun a => ?_)
    rw [mixedGaussianSchwartz_apply]
    have hv : ((idealLatticeEquiv K I a : idealLattice K I) : minkowskiSpace K)
        = toMinkowski K (mixedEmbedding K (a : K)) := rfl
    rw [hv, ContinuousLinearEquiv.symm_apply_apply]
  -- Dual lattice reindexing equiv `(𝔞𝔡)⁻¹ ≃ dualLattice Λ(𝔞)` via `conjMink ∘ eEmb`.
  let φD := fun (a : (dualIdeal K 𝔞 : Submodule (𝓞 K) K)) =>
    (⟨conjMink K (eEmb K (a : K)), by
      rw [dualLattice_idealLattice K 𝔞 hne]
      exact Submodule.mem_map.mpr ⟨eEmb K (a : K),
        (mem_idealLattice_iff K (dualIdeal K 𝔞) _).mpr ⟨(a : K), a.2, rfl⟩, rfl⟩⟩ :
      PoissonSummation.dualLattice (idealLattice K I))
  have hφD_inj : Function.Injective φD := by
    intro a b h
    have h1 : conjMink K (eEmb K (a : K)) = conjMink K (eEmb K (b : K)) := Subtype.ext_iff.mp h
    exact Subtype.ext (eEmb_injective K ((conjMink K).injective h1))
  have hφD_surj : Function.Surjective φD := by
    rintro ⟨w, hw⟩
    rw [dualLattice_idealLattice K 𝔞 hne] at hw
    obtain ⟨u, hu, hφu⟩ := Submodule.mem_map.mp hw
    obtain ⟨b, hb, hbu⟩ := (mem_idealLattice_iff K (dualIdeal K 𝔞) u).mp hu
    refine ⟨⟨b, hb⟩, ?_⟩
    apply Subtype.ext
    show conjMink K (eEmb K b) = w
    rw [hbu]; exact hφu
  let eD := Equiv.ofBijective φD ⟨hφD_inj, hφD_surj⟩
  -- Dual side: `∑_{w ∈ Λ(𝔞)*} 𝓕 f w = |N(x)| · (Θ((𝔞𝔡)⁻¹, x) + 1)`.
  have hDsum : ∑' w : PoissonSummation.dualLattice (idealLattice K I),
        (mixedGaussian K (x * (toMinkowski K).symm (w : minkowskiSpace K)) : ℂ)
      = 1 + mixedThetaKernel K (dualIdeal K 𝔞) x := by
    rw [← tsum_mixedGaussian_submodule K (dualIdeal K 𝔞) hD hx,
      ← Equiv.tsum_eq eD
        (fun w : PoissonSummation.dualLattice (idealLattice K I) =>
          (mixedGaussian K (x * (toMinkowski K).symm (w : minkowskiSpace K)) : ℂ))]
    refine tsum_congr (fun a => ?_)
    have hval : ((eD a : PoissonSummation.dualLattice (idealLattice K I)) : minkowskiSpace K)
        = conjMink K (eEmb K (a : K)) := rfl
    rw [hval]
    have hpre : (eEmbℝ K).symm (eEmb K (a : K)) = mixedEmbedding K (a : K) := by
      rw [← eEmbℝ_mixedEmbedding K (a : K), ContinuousLinearEquiv.symm_apply_apply]
    have h1 : conjMink K (eEmb K (a : K))
        = toMinkowski K (conjMixed K (mixedEmbedding K (a : K))) := by
      rw [conjMink_apply, hpre]
    rw [h1, ContinuousLinearEquiv.symm_apply_apply, mixedGaussian_mul_conjMixed]
  have hdual : ∑' w : PoissonSummation.dualLattice (idealLattice K I),
        𝓕 (mixedGaussianSchwartz K hxinv : minkowskiSpace K → ℂ) (w : minkowskiSpace K)
      = ((|mixedEmbedding.norm x| : ℝ) : ℂ) * (mixedThetaKernel K (dualIdeal K 𝔞) x + 1) := by
    have hpt : ∀ w : PoissonSummation.dualLattice (idealLattice K I),
        𝓕 (mixedGaussianSchwartz K hxinv : minkowskiSpace K → ℂ) (w : minkowskiSpace K)
          = ((|mixedEmbedding.norm x| : ℝ) : ℂ) *
              (mixedGaussian K (x * (toMinkowski K).symm (w : minkowskiSpace K)) : ℂ) := by
      intro w
      have hFeq : (mixedGaussianSchwartz K hxinv : minkowskiSpace K → ℂ)
          = fun v => (mixedGaussian K (x⁻¹ * (toMinkowski K).symm v) : ℂ) := by
        funext v; exact mixedGaussianSchwartz_apply K hxinv v
      rw [hFeq, fourier_mixedGaussian_scaling K x⁻¹ hxinv (w : minkowskiSpace K), hAbs, inv_inv]
    rw [tsum_congr hpt, tsum_mul_left, hDsum, add_comm (1 : ℂ)]
  -- Combine, identify the covolume, and solve for `Θ(𝔞, x⁻¹)`.
  rw [hprimal, hdual] at hPoisson
  have hcov : ZLattice.covolume (idealLattice K I) = covolume K 𝔞 := by
    rw [hIdef]; exact covolume_idealLattice K 𝔞 hne
  rw [hcov] at hPoisson
  have hgoaldiv : ((|mixedEmbedding.norm x| / covolume K 𝔞 : ℝ) : ℂ)
      = ((|mixedEmbedding.norm x| : ℝ) : ℂ) / ((covolume K 𝔞 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hgoaldiv]
  linear_combination hPoisson
end DedekindZeta.Theta
