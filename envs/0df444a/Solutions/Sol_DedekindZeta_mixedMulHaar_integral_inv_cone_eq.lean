-- Prove2me | solution 1 for DedekindZeta.mixedMulHaar_integral_inv_cone_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:13.40417+00:00
-- url     : https://prove2.me/submissions/42869f1a-dedb-4ef5-89f8-aaabab315a43

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_measurable_mixedSpace_inv
import Theorems.Thm_DedekindZeta_isFundamentalDomain_inv_image_fundamentalCone
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_coneSMul_def
import Theorems.Thm_DedekindZeta_isFundamentalDomain_fundamentalCone
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
namespace DedekindZeta
theorem _root_.solution
    (h : mixedEmbedding.mixedSpace K → ℂ)
    (hinv : ∀ (u : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K), h (u • x) = h x)
    (hmeas : AEStronglyMeasurable h (mixedMulHaar K))
    (hint : Integrable
      ((mixedEmbedding.fundamentalCone K).indicator h) (mixedMulHaar K)) :
    ∫ x, ((fun y => y⁻¹) '' mixedEmbedding.fundamentalCone K).indicator h x
          ∂(mixedMulHaar K)
      = ∫ x, (mixedEmbedding.fundamentalCone K).indicator h x ∂(mixedMulHaar K) := by
  classical
  haveI : Countable (Multiplicative (Fin (rank K) → ℤ)) :=
    inferInstanceAs (Countable (Fin (rank K) → ℤ))
  -- The inverse image is a measurable set: inversion is involutive, so the image
  -- equals the preimage of the (measurable) cone under the measurable map `·⁻¹`.
  have himg_eq : (fun y : mixedEmbedding.mixedSpace K => y⁻¹) ''
        mixedEmbedding.fundamentalCone K
      = (fun y : mixedEmbedding.mixedSpace K => y⁻¹) ⁻¹'
        mixedEmbedding.fundamentalCone K := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨x⁻¹, hx, inv_inv x⟩
  have hmeas_img : MeasurableSet ((fun y : mixedEmbedding.mixedSpace K => y⁻¹) ''
      mixedEmbedding.fundamentalCone K) := by
    rw [himg_eq]
    exact measurable_mixedSpace_inv (measurableSet_fundamentalCone K)
  -- `h` is invariant under the acting group `Multiplicative (Fin (rank K) → ℤ)`,
  -- since `g • x = coneUnitHom g • x` and `h` is `(𝓞 K)ˣ`-invariant by `hinv`.
  have hG : ∀ (g : Multiplicative (Fin (rank K) → ℤ))
      (x : mixedEmbedding.mixedSpace K), h (g • x) = h x := by
    intro g x
    rw [coneSMul_def]
    exact hinv (coneUnitHom (K := K) g) x
  -- Both the cone and its inverse image are fundamental domains for the same
  -- action and measure, so the integral of the invariant `h` agrees.
  rw [integral_indicator hmeas_img,
    integral_indicator (measurableSet_fundamentalCone K),
    (isFundamentalDomain_inv_image_fundamentalCone (K := K)).setIntegral_eq
      (isFundamentalDomain_fundamentalCone (K := K)) hG]
end DedekindZeta
