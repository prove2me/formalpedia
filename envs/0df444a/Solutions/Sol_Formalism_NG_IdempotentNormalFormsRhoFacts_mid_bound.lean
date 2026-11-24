-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsRhoFacts.mid_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:23.003607+00:00
-- url     : https://prove2.me/submissions/53359037-931d-4de4-9a6d-a7a54a4169fb

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Theorems.Thm_Formalism_NG_torsLen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentNormalFormsRhoFacts
namespace Formalism.NG.IdempotentNormalFormsRhoFacts
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type*}
    [Group G] {d : Type} [Fintype d] (ρM : Representation O G (d → KO O)) {H : Type*}
    [AddCommGroup H] [Module O H] (Ψ : H →ₗ[O] coZ1s ρM) (δ : O)
    (hcob : ∀ h : H, ∀ v : d → KO O, (Ψ h : G → (d → KO O)) = coD0 ρM v → (δ * δ) • v = 0) :
    Module.length O ↥(LinearMap.range Ψ ⊓
        LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ) ≤
      (Fintype.card d : ℕ∞) * (2 * IsDiscreteValuationRing.addVal O δ) := by
  set T := LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) (δ * δ))
  have hle : ∀ z : ↥(LinearMap.range Ψ ⊓
      LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ),
      (z.1 : G → (d → KO O)) ∈ T.map (coD0 ρM) := by
    rintro ⟨z, hz⟩
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
    obtain ⟨h, rfl⟩ := LinearMap.mem_range.mp hz1
    have h3 : Ψ h ∈ (coB1 ρM).comap (coZ1s ρM).subtype := by
      rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz2
      exact hz2
    rw [Submodule.mem_comap, Submodule.subtype_apply, coB1, LinearMap.mem_range] at h3
    obtain ⟨v, hv⟩ := h3
    refine Submodule.mem_map.mpr ⟨v, LinearMap.mem_ker.mpr ?_, hv⟩
    simpa using hcob h v hv.symm
  calc _ ≤ Module.length O ↥(T.map (coD0 ρM)) := by
        refine Module.length_le_of_injective
          (((coZ1s ρM).subtype ∘ₗ Submodule.subtype _).codRestrict _ hle) ?_
        intro x y hxy
        have := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext this)
    _ ≤ Module.length O T :=
        Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective _ _)
    _ = _ := torsLen O d δ
end Formalism.NG.IdempotentNormalFormsRhoFacts
