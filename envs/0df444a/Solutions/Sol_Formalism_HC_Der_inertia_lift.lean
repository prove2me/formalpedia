-- Prove2me | solution 1 for Formalism.HC.Der.inertia_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:41:18.501846+00:00
-- url     : https://prove2.me/submissions/916a6d1b-0de6-4508-a8ff-d1ebbcc428f2

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Theorems.Thm_Formalism_HC_Der_res_smul
import Theorems.Thm_Formalism_HC_Der_mem_over_iff
import Theorems.Thm_Formalism_HC_Der_smul_mem_of_inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_mem_stab_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsScalarTower ℚ E L]
namespace Formalism.HC.Der
theorem _root_.solution [IsGalois ℚ L] (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver P] (σ : E ≃ₐ[ℚ] E)
    (hσ : ∀ x : 𝓞 E, σ • x - x ∈ P) :
    ∃ τ : L ≃ₐ[ℚ] L, (∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) ∧ ∀ y : 𝓞 L, τ • y - y ∈ Q := by
  have : IsGalois E L := IsGalois.tower_top_of_isGalois ℚ E L
  have hinv : Algebra.IsInvariant (𝓞 E) (𝓞 L) (L ≃ₐ[E] L) := inferInstance
  let τ₀ : L ≃ₐ[ℚ] L := σ.liftNormal L
  have h₀ : ∀ x, algebraMap E L (σ x) = τ₀ (algebraMap E L x) := fun x => (AlgEquiv.liftNormal_commutes σ L x).symm
  have hunder : (τ₀⁻¹ • Q).under (𝓞 E) = Q.under (𝓞 E) := by
    ext a
    rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff,
      ← res_smul σ τ₀ h₀, ← mem_over_iff P Q, ← mem_over_iff P Q]
    exact smul_mem_of_inertia σ P hσ a
  obtain ⟨ρ, hρ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 E) (𝓞 L) (L ≃ₐ[E] L) Q (τ₀⁻¹ • Q) hunder.symm
  let τ₁ : L ≃ₐ[ℚ] L := τ₀ * ρ.restrictScalars ℚ
  have hs : ∀ (r : L ≃ₐ[E] L) (y : 𝓞 L), (r.restrictScalars ℚ) • y = r • y := fun _ _ => rfl
  have h₁ : ∀ x, algebraMap E L (σ x) = τ₁ (algebraMap E L x) := fun x => by
    show _ = τ₀ (ρ (algebraMap E L x))
    rw [ρ.commutes, h₀]
  have hst : τ₁ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q := by
    refine Decomp.mem_stab_of τ₁ Q fun z => ?_
    rw [mul_smul, hs, ← Ideal.mem_inv_pointwise_smul_iff, hρ]
    exact Ideal.smul_mem_pointwise_smul_iff
  let f : (𝓞 L ⧸ Q) ≃ₐ[𝓞 E ⧸ P] (𝓞 L ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := (Ideal.Quotient.stabilizerHom Q (Q.under ℤ) (L ≃ₐ[ℚ] L) ⟨τ₁, hst⟩).toRingEquiv) (by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show Ideal.Quotient.mk Q (τ₁ • algebraMap (𝓞 E) (𝓞 L) a) = Ideal.Quotient.mk Q (algebraMap (𝓞 E) (𝓞 L) a)
      rw [Ideal.Quotient.eq, ← res_smul σ τ₁ h₁, ← map_sub, ← mem_over_iff P Q]
      exact hσ a)
  obtain ⟨r, hr⟩ := Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[E] L) P Q f
  refine ⟨τ₁ * (r.1⁻¹).restrictScalars ℚ, fun x => ?_, fun y => ?_⟩
  · show _ = τ₁ ((r.1⁻¹) (algebraMap E L x))
    rw [AlgEquiv.commutes, h₁]
  · have h2 : Ideal.Quotient.mk Q (r.1 • (r.1⁻¹ • y)) = Ideal.Quotient.mk Q (τ₁ • (r.1⁻¹ • y)) :=
      DFunLike.congr_fun hr (Ideal.Quotient.mk Q (r.1⁻¹ • y))
    rw [smul_inv_smul] at h2
    rw [mul_smul, hs, ← Ideal.Quotient.eq]
    exact h2.symm
end Formalism.HC.Der
