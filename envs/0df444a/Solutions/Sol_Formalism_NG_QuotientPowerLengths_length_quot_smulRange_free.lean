-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.length_quot_smulRange_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:11.905241+00:00
-- url     : https://prove2.me/submissions/c50725a1-caff-438e-b9f8-1e2170ee0940

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_mem_smulRange
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_length_quot_smulRange_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.NG.QuotientPowerLengths
theorem _root_.solution (Q : Type*) [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    [IsTorsionFree O Q] (l : O) :
    Module.length O (Q ⧸ smulRange Q l) = finrank O Q * addVal O l := by
  haveI : NoZeroSMulDivisors O Q := by
    refine ⟨fun {c x} h => ?_⟩
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have hreg : IsRegular c := isRegular_of_ne_zero hc
      apply (‹IsTorsionFree O Q›).1 hreg
      show c • x = c • 0
      rw [h, smul_zero]
  haveI : Module.Free O Q := by
    first
      | exact Module.free_of_finite_type_torsion_free'
      | infer_instance
  let e : Q ≃ₗ[O] (Fin (finrank O Q) → O) := (Module.finBasis O Q).equivFun
  have hmap : (smulRange Q l).map (e : Q →ₗ[O] (Fin (finrank O Q) → O)) =
      smulRange (Fin (finrank O Q) → O) l := by
    ext x
    rw [Submodule.mem_map, mem_smulRange]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨y, rfl⟩ := (mem_smulRange l q).mp hq
      exact ⟨e y, by simp⟩
    · rintro ⟨y, rfl⟩
      exact ⟨l • e.symm y, (mem_smulRange l _).mpr ⟨_, rfl⟩, by simp⟩
  let e' := Submodule.Quotient.equiv (smulRange Q l) (smulRange (Fin (finrank O Q) → O) l) e hmap
  rw [← length_quot_smulRange_pi (finrank O Q) l]
  first
    | exact e'.length_eq
    | exact le_antisymm (Module.length_le_of_injective e'.toLinearMap e'.injective)
        (Module.length_le_of_injective e'.symm.toLinearMap e'.symm.injective)
end Formalism.NG.QuotientPowerLengths
