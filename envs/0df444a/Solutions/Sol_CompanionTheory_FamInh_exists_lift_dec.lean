-- Prove2me | solution 1 for CompanionTheory.FamInh.exists_lift_dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:43:02.349624+00:00
-- url     : https://prove2.me/submissions/6de46696-9ccb-4374-83fe-6353fad16d40

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_CompanionTheory_AutomorphicTheory_PlaceSeparation_ArtinA
import Theorems.Thm_CompanionTheory_FamInh_coe_res_smul
import Theorems.Thm_CompanionTheory_FamInh_res_restrictScalars
import Theorems.Thm_ReciprocityTheory_Gal_exists_smul_eq_of_over
import Theorems.Thm_ReciprocityTheory_Gal_smul_valuation_lt_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open CompanionTheory CompanionTheory.FamInh
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
variable [IsGalois K L]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
namespace CompanionTheory.FamInh
theorem _root_.solution (hw : IsPlaceOver A w) {τ : L ≃ₐ[K] L}
    (hτ : τ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    ∃ σ ∈ Dec (F := K) A, AlgEquiv.restrictNormalHom L σ = τ := by
  obtain ⟨σ0, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω) τ
  have h1 : ∀ x : 𝓞 L, (σ0 • A).valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ w.asIdeal := by
    intro x
    rw [smul_valuation_lt_one_iff, ← coe_res_smul, hw, map_inv, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      MulAction.mem_stabilizer_iff.1 hτ]
  obtain ⟨g, hg⟩ := exists_smul_eq_of_over (F := L) h1 hw
  refine ⟨g.restrictScalars K * σ0, ?_, ?_⟩
  · rw [mem_Dec, mul_smul]
    exact hg
  · rw [map_mul, res_restrictScalars, one_mul]
end CompanionTheory.FamInh
